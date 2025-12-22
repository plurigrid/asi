;;; crdt-vterm-bridge.el --- Bridge CRDT remote-insert to vterm sharing -*- lexical-binding: t; -*-

;; This bridges crdt.el's CRDT operations with vterm terminal sharing.
;; 
;; Challenge: crdt.el operates on text buffers with CRDT IDs per character.
;; vterm is a process buffer where:
;;   1. Output comes from PTY (not user edits)
;;   2. Input goes to PTY (not buffer modifications)
;;   3. Terminal state (cursor, colors, scrollback) isn't text
;;
;; Solution: Intercept at the PTY layer, not the buffer layer.
;; Use a "shadow buffer" for CRDT sync of terminal output.

(require 'vterm)
(require 'crdt)

;;; Configuration

(defgroup crdt-vterm nil
  "CRDT sharing for vterm terminals."
  :group 'crdt
  :group 'vterm)

(defcustom crdt-vterm-sync-interval 0.05
  "Interval in seconds for syncing vterm output to CRDT."
  :type 'number)

(defcustom crdt-vterm-input-mode 'broadcast
  "How to handle input from remote users.
- `broadcast': All input goes to the shared terminal
- `read-only': Remote users can only watch
- `gf3-trifurcate': Input routed by GF(3) trit assignment"
  :type '(choice (const broadcast) (const read-only) (const gf3-trifurcate)))

;;; State

(defvar-local crdt-vterm--shadow-buffer nil
  "Buffer mirroring vterm output for CRDT sync.")

(defvar-local crdt-vterm--last-sync-point 1
  "Point up to which we've synced to CRDT.")

(defvar-local crdt-vterm--sync-timer nil
  "Timer for periodic CRDT sync.")

(defvar-local crdt-vterm--input-queue nil
  "Queue of remote inputs waiting to be sent.")

(defvar-local crdt-vterm--gf3-trit nil
  "GF(3) trit assignment for this terminal session.")

;;; GF(3) Color Assignment (from Gay.jl pattern)

(defun crdt-vterm--splitmix64-hash (seed)
  "Simple hash for GF(3) assignment."
  (let* ((z (logxor seed (ash seed -16))))
    (logand z #x7FFFFFFF)))

(defun crdt-vterm--gf3-trit (seed)
  "Get GF(3) trit from SEED: :MINUS, :ERGODIC, or :PLUS."
  (pcase (mod (abs (crdt-vterm--splitmix64-hash seed)) 3)
    (0 :MINUS)
    (1 :ERGODIC)
    (2 :PLUS)))

;;; Shadow Buffer Management

(defun crdt-vterm--create-shadow-buffer (vterm-buf)
  "Create shadow buffer for VTERM-BUF."
  (let ((shadow-name (format "*crdt-vterm-shadow:%s*" (buffer-name vterm-buf))))
    (with-current-buffer (get-buffer-create shadow-name)
      (setq-local crdt-vterm--source-buffer vterm-buf)
      (current-buffer))))

(defun crdt-vterm--sync-to-shadow ()
  "Sync vterm visible text to shadow buffer for CRDT."
  (when (and crdt-vterm--shadow-buffer (buffer-live-p crdt-vterm--shadow-buffer))
    (let ((vterm-text (buffer-substring-no-properties 
                       crdt-vterm--last-sync-point 
                       (point-max))))
      (when (> (length vterm-text) 0)
        (with-current-buffer crdt-vterm--shadow-buffer
          (goto-char (point-max))
          (insert vterm-text))
        (setq crdt-vterm--last-sync-point (point-max))))))

;;; CRDT Integration

(defun crdt-vterm--format-remote-insert (content site-id)
  "Format CONTENT as CRDT remote-insert sexp."
  (let* ((timestamp (float-time))
         (id (format "%08x" (abs (crdt-vterm--splitmix64-hash 
                                  (sxhash (format "%s:%s" content timestamp))))))
         (trit (crdt-vterm--gf3-trit (sxhash content))))
    `(remote-insert ,id ,site-id ,content 
                    (props :type :terminal-output
                           :trit ,trit
                           :timestamp ,timestamp))))

(defun crdt-vterm--handle-remote-input (input-sexp)
  "Handle INPUT-SEXP from remote CRDT peer."
  (pcase input-sexp
    (`(remote-input ,_id ,user-id ,input-str ,props)
     (pcase crdt-vterm-input-mode
       ('broadcast
        (vterm-send-string input-str))
       ('read-only
        (message "crdt-vterm: read-only mode, ignoring input from %s" user-id))
       ('gf3-trifurcate
        ;; Only accept if trit matches our assignment
        (let ((input-trit (plist-get props :trit)))
          (when (eq input-trit crdt-vterm--gf3-trit)
            (vterm-send-string input-str))))))))

;;; Timer-based sync

(defun crdt-vterm--start-sync ()
  "Start periodic sync timer."
  (when crdt-vterm--sync-timer
    (cancel-timer crdt-vterm--sync-timer))
  (setq crdt-vterm--sync-timer
        (run-with-timer 
         crdt-vterm-sync-interval
         crdt-vterm-sync-interval
         (lambda ()
           (when (buffer-live-p (current-buffer))
             (crdt-vterm--sync-to-shadow))))))

(defun crdt-vterm--stop-sync ()
  "Stop periodic sync timer."
  (when crdt-vterm--sync-timer
    (cancel-timer crdt-vterm--sync-timer)
    (setq crdt-vterm--sync-timer nil)))

;;; Main Entry Points

;;;###autoload
(defun crdt-vterm-share ()
  "Share current vterm buffer via CRDT."
  (interactive)
  (unless (derived-mode-p 'vterm-mode)
    (user-error "Not in a vterm buffer"))
  
  ;; Create shadow buffer
  (setq crdt-vterm--shadow-buffer (crdt-vterm--create-shadow-buffer (current-buffer)))
  
  ;; Assign GF(3) trit for this session
  (setq crdt-vterm--gf3-trit (crdt-vterm--gf3-trit (sxhash (buffer-name))))
  
  ;; Share the shadow buffer via CRDT
  (with-current-buffer crdt-vterm--shadow-buffer
    (call-interactively #'crdt-share-buffer))
  
  ;; Start sync
  (crdt-vterm--start-sync)
  
  (message "crdt-vterm: Sharing terminal with GF(3) trit %s" crdt-vterm--gf3-trit))

;;;###autoload
(defun crdt-vterm-stop-share ()
  "Stop sharing current vterm buffer."
  (interactive)
  (crdt-vterm--stop-sync)
  (when (and crdt-vterm--shadow-buffer (buffer-live-p crdt-vterm--shadow-buffer))
    (with-current-buffer crdt-vterm--shadow-buffer
      (when crdt-mode
        (crdt-stop-share-buffer)))
    (kill-buffer crdt-vterm--shadow-buffer))
  (setq crdt-vterm--shadow-buffer nil)
  (message "crdt-vterm: Stopped sharing"))

;;; Babashka Sexp Replay

(defvar crdt-vterm-replay-buffer nil
  "Buffer for replaying CRDT terminal sessions.")

(defun crdt-vterm--parse-sexp-file (file)
  "Parse FILE containing CRDT terminal sexps."
  (with-temp-buffer
    (insert-file-contents file)
    (goto-char (point-min))
    (let (sexps)
      (condition-case nil
          (while t
            (push (read (current-buffer)) sexps))
        (end-of-file nil))
      (nreverse sexps))))

(defun crdt-vterm--replay-sexp (sexp vterm-buf)
  "Replay SEXP into VTERM-BUF."
  (pcase sexp
    (`(remote-insert ,_id ,_site ,content . ,_)
     (with-current-buffer vterm-buf
       (goto-char (point-max))
       (insert content "\n")))
    (`(remote-input ,_id ,_user ,input . ,_)
     (with-current-buffer vterm-buf
       (when (derived-mode-p 'vterm-mode)
         (vterm-send-string input))))))

;;;###autoload
(defun crdt-vterm-replay (sexp-file &optional speed)
  "Replay CRDT terminal session from SEXP-FILE at SPEED (1.0 = realtime)."
  (interactive "fSexp file: \nnSpeed (1.0 = realtime): ")
  (let ((speed (or speed 1.0))
        (sexps (crdt-vterm--parse-sexp-file sexp-file))
        (buf (get-buffer-create "*crdt-vterm-replay*")))
    (pop-to-buffer buf)
    (erase-buffer)
    (let ((start-ts nil))
      (dolist (sexp sexps)
        (pcase sexp
          (`(crdt-terminal-session . ,_)
           (insert ";; Session: " (format "%S" sexp) "\n\n"))
          (`(remote-insert ,_id ,_site ,content (props . ,props))
           (let ((ts (plist-get props :timestamp)))
             (when ts
               (unless start-ts (setq start-ts ts))
               (let ((delay (/ (- ts start-ts) speed 1000.0)))
                 (when (> delay 0)
                   (sit-for (min delay 0.5)))))
             (insert content "\n")
             (redisplay))))))))

;;; P2P Sharing via localsend-mcp

(defvar crdt-vterm-localsend-session nil
  "Active localsend session for terminal sharing.")

(defun crdt-vterm-localsend-share ()
  "Share terminal session via localsend P2P."
  (interactive)
  (unless (derived-mode-p 'vterm-mode)
    (user-error "Not in a vterm buffer"))
  (let* ((sexp-file (make-temp-file "crdt-vterm-" nil ".sexp"))
         (session-id (format "T-%s" (substring (md5 (buffer-name)) 0 8))))
    (setq crdt-vterm-localsend-session
          `(:file ,sexp-file :session ,session-id :buffer ,(current-buffer)))
    ;; Start recording to file
    (setq crdt-vterm--shadow-buffer (crdt-vterm--create-shadow-buffer (current-buffer)))
    (crdt-vterm--start-sync)
    ;; Would call localsend-mcp here to advertise
    (message "crdt-vterm: Sharing via localsend, session %s, file %s" 
             session-id sexp-file)))

;;; GF(3) Trifurcated Multi-User Input

(defvar crdt-vterm-input-queues
  '((:MINUS . nil) (:ERGODIC . nil) (:PLUS . nil))
  "Input queues per GF(3) trit for trifurcated routing.")

(defun crdt-vterm--route-input-by-trit (input trit)
  "Route INPUT to queue based on TRIT."
  (let ((queue (assq trit crdt-vterm-input-queues)))
    (when queue
      (setcdr queue (append (cdr queue) (list input))))))

(defun crdt-vterm--process-trit-queue (trit)
  "Process all inputs in queue for TRIT."
  (let* ((queue (assq trit crdt-vterm-input-queues))
         (inputs (cdr queue)))
    (when inputs
      (setcdr queue nil)
      (dolist (input inputs)
        (vterm-send-string input)))))

(defun crdt-vterm-trifurcate-cycle ()
  "Cycle through GF(3) queues: MINUS -> ERGODIC -> PLUS."
  (interactive)
  (crdt-vterm--process-trit-queue :MINUS)
  (sit-for 0.01)
  (crdt-vterm--process-trit-queue :ERGODIC)
  (sit-for 0.01)
  (crdt-vterm--process-trit-queue :PLUS))

;;; Alternative: Direct PTY Intercept (more complex but lower latency)
;;
;; For true collaborative terminals, you'd intercept at:
;; 1. vterm--filter-buffer-substring (outgoing text)
;; 2. vterm-send-* functions (incoming input)
;;
;; This requires modifying vterm's C library or using a PTY wrapper like:
;; - tmux/screen with shared sockets
;; - tmate (cloud-based tmux sharing)
;; - termpair (Python web-based terminal sharing)

(defun crdt-vterm--advice-send-string (orig-fn string &rest args)
  "Advice to broadcast input strings to CRDT peers."
  (when (and crdt-vterm--shadow-buffer crdt-mode)
    (let ((input-sexp (crdt-vterm--format-remote-insert 
                       string 
                       (crdt--session-local-id crdt--session))))
      ;; In a real implementation, this would broadcast to peers
      (message "crdt-vterm: would broadcast %S" input-sexp)))
  (apply orig-fn string args))

;; Uncomment to enable input broadcasting:
;; (advice-add 'vterm-send-string :around #'crdt-vterm--advice-send-string)

(provide 'crdt-vterm-bridge)
;;; crdt-vterm-bridge.el ends here
