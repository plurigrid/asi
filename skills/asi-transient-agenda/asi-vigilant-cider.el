;; Vigilant CIDER: nREPL Hijack Detection + Socket Integrity Monitoring
;; "others will try to do the same and eat you be vigilant"
;; Detects: non-localhost connections, eval source boundary crossing, port manipulation

(require 'cider-mode)
(require 'nrepl-client)

;; ═══════════════════════════════════════════════════════════
;; 1. VIGILANCE STATE & AUDIT LOG
;; ═══════════════════════════════════════════════════════════

(defvar asi-vigilant--audit-log nil
  "Audit log of all nREPL operations and security events.")

(defvar asi-vigilant--trusted-hosts '("127.0.0.1" "localhost" "::1")
  "List of trusted nREPL host addresses.")

(defvar asi-vigilant--verified-ports '(1667)
  "List of verified/expected nREPL ports.")

(defvar asi-vigilant--eval-boundaries nil
  "Track eval source boundaries to detect cross-boundary evaluation.")

(defvar asi-vigilant--hijack-attempts 0
  "Count of detected hijack attempts.")

(defvar asi-vigilant--sentinel-active t
  "Whether vigilance sentinel is monitoring.")

;; ═══════════════════════════════════════════════════════════
;; 2. HIJACK DETECTION: Non-localhost connections
;; ═══════════════════════════════════════════════════════════

(defun asi-vigilant--check-connection-safety (host port)
  "Check if nREPL connection to HOST:PORT is trusted."
  (let* ((is-trusted-host (member host asi-vigilant--trusted-hosts))
         (is-verified-port (member port asi-vigilant--verified-ports))
         (safe (and is-trusted-host is-verified-port)))

    ;; Log the connection attempt
    (push (list 'connection-check
                (current-time)
                host port
                (if safe "SAFE" "HIJACK-ALERT"))
          asi-vigilant--audit-log)

    ;; Alert if untrusted
    (unless safe
      (incf asi-vigilant--hijack-attempts)
      (message "⚠️  VIGILANT: nREPL connection to %s:%d SUSPICIOUS (not localhost+verified port)"
               host port)
      (when (> asi-vigilant--hijack-attempts 3)
        (message "🛑 VIGILANT: 3+ hijack attempts detected. Disconnecting CIDER.")))

    safe))

(defadvice cider-connect-clj (before asi-vigilant-hijack-check (params))
  "Check for hijack before connecting CIDER to nREPL."
  (let ((host (plist-get params :host))
        (port (plist-get params :port)))
    (unless (asi-vigilant--check-connection-safety host port)
      (user-error "🛑 VIGILANT: Attempted connection to untrusted host %s:%d blocked. Are you being hijacked?"
                  host port))))

;; ═══════════════════════════════════════════════════════════
;; 3. EVAL SOURCE BOUNDARY MONITORING
;; ═══════════════════════════════════════════════════════════

(defun asi-vigilant--record-source-file (file)
  "Record the source file for boundary tracking."
  (push (list 'source-file file (current-time))
        asi-vigilant--eval-boundaries))

(defun asi-vigilant--check-eval-boundary (code context-file)
  "Check if CODE is being evaluated from correct source file."
  (let* ((expected-file (or (car (car asi-vigilant--eval-boundaries)) nil))
         (boundary-crossed (and expected-file
                               context-file
                               (not (string= expected-file context-file)))))

    (when boundary-crossed
      (push (list 'boundary-crossing
                  (current-time)
                  code
                  (list :expected expected-file :actual context-file)
                  "ALERT")
            asi-vigilant--audit-log)
      (message "⚠️  VIGILANT: Eval boundary crossed! Expected %s, got %s"
               expected-file context-file))))

(defadvice cider-eval-region (before asi-vigilant-boundary-check (start end))
  "Detect eval source boundary crossing before evaluation."
  (let* ((context-file (buffer-file-name))
         (code (buffer-substring start end)))
    (asi-vigilant--check-eval-boundary code context-file)))

;; ═══════════════════════════════════════════════════════════
;; 4. SOCKET INTEGRITY: Monitor nREPL writes/reads
;; ═══════════════════════════════════════════════════════════

(defvar asi-vigilant--socket-state nil
  "Track socket state: (host port pid open-time last-activity)")

(defun asi-vigilant--monitor-socket-activity (op data)
  "Monitor socket activity: 'send or 'recv with data."
  (let* ((now (current-time))
         (timestamp (format-time-string "%H:%M:%S" now)))
    (push (list 'socket-op op timestamp (length data) (md5 data))
          asi-vigilant--audit-log)

    ;; Detect anomalies: large unexpected messages, rapid-fire sends
    (let ((data-size (length data)))
      (when (> data-size 100000)  ;; 100KB threshold
        (message "⚠️  VIGILANT: Large socket write (%dB) — possible buffer overflow attempt?"
                 data-size)))))

(defadvice nrepl-send-request (after asi-vigilant-socket-monitor (request callback))
  "Monitor nREPL socket writes for anomalies."
  (asi-vigilant--monitor-socket-activity 'send (pp-to-string request)))

;; ═══════════════════════════════════════════════════════════
;; 5. SENTINEL PROCESS: Continuous integrity check
;; ═══════════════════════════════════════════════════════════

(defun asi-vigilant--sentinel ()
  "Background sentinel to detect anomalies in nREPL state."
  (when asi-vigilant--sentinel-active
    (let* ((repl-buf (get-buffer "*cider-repl babashka*"))
           (proc (and repl-buf (get-buffer-process repl-buf))))

      ;; Check if process is alive and connected
      (when proc
        (unless (eq (process-status proc) 'open)
          (message "🛑 VIGILANT: nREPL connection lost or hijacked. Status: %s"
                   (process-status proc))))

      ;; Check for unexpected process substitution (someone replacing our nREPL)
      (when (and proc repl-buf)
        (let ((host (process-contact proc :host))
              (port (process-contact proc :service)))
          (unless (asi-vigilant--check-connection-safety host port)
            (message "🛑 VIGILANT ALERT: nREPL process swapped to untrusted endpoint!")
            (set-process-sentinel proc nil)  ;; stop monitoring hijacked process
            (kill-buffer repl-buf)))))))

(defvar asi-vigilant--sentinel-timer nil
  "Timer for background sentinel checks.")

(defun asi-vigilant-enable ()
  "Enable all vigilance monitoring."
  (interactive)
  (setq asi-vigilant--sentinel-active t)
  ;; Run sentinel every 5 seconds
  (setq asi-vigilant--sentinel-timer
        (run-at-time 5 5 #'asi-vigilant--sentinel))

  ;; Enable advice
  (ad-enable-advice 'cider-connect-clj 'before 'asi-vigilant-hijack-check)
  (ad-enable-advice 'cider-eval-region 'before 'asi-vigilant-boundary-check)
  (ad-enable-advice 'nrepl-send-request 'after 'asi-vigilant-socket-monitor)
  (ad-activate 'cider-connect-clj)
  (ad-activate 'cider-eval-region)
  (ad-activate 'nrepl-send-request)

  (message "✅ Vigilant CIDER enabled. Monitoring nREPL hijack attempts."))

(defun asi-vigilant-disable ()
  "Disable vigilance monitoring."
  (interactive)
  (setq asi-vigilant--sentinel-active nil)
  (when asi-vigilant--sentinel-timer
    (cancel-timer asi-vigilant--sentinel-timer))
  (ad-disable-advice 'cider-connect-clj 'before 'asi-vigilant-hijack-check)
  (ad-disable-advice 'cider-eval-region 'before 'asi-vigilant-boundary-check)
  (ad-disable-advice 'nrepl-send-request 'after 'asi-vigilant-socket-monitor)
  (message "❌ Vigilant CIDER disabled."))

;; ═══════════════════════════════════════════════════════════
;; 6. AUDIT LOG DISPLAY
;; ═══════════════════════════════════════════════════════════

(defun asi-vigilant-show-audit-log ()
  "Display the security audit log."
  (interactive)
  (let ((buf (get-buffer-create "*CIDER Vigilance Audit*")))
    (with-current-buffer buf
      (read-only-mode -1)
      (erase-buffer)
      (insert "#+TITLE: CIDER Vigilance Audit Log\n")
      (insert (format "#+DATE: %s\n" (current-time-string)))
      (insert (format "Hijack attempts: %d\n\n" asi-vigilant--hijack-attempts))

      (insert "| Time | Event Type | Details |\n")
      (insert "|------|------------|---------|\n")

      (dolist (entry (reverse asi-vigilant--audit-log))
        (let ((event-type (nth 0 entry))
              (time (format-time-string "%H:%M:%S" (nth 1 entry)))
              (data (nth 2 entry)))
          (insert (format "| %s | %s | %s |\n" time event-type data))))

      (org-mode)
      (goto-char (point-min))
      (read-only-mode 1))
    (switch-to-buffer buf)))

;; ═══════════════════════════════════════════════════════════
;; 7. CIDER MODE INTEGRATION
;; ═══════════════════════════════════════════════════════════

(defun asi-cider-setup ()
  "Set up CIDER with vigilance monitoring."
  (interactive)
  (asi-vigilant-enable)
  (message "CIDER setup complete. Use M-x asi-vigilant-show-audit-log to view security events."))

(defun asi-cider-eval-region-safe (start end)
  "Evaluate region with vigilance guards."
  (interactive "r")
  (let ((code (buffer-substring start end))
        (file (buffer-file-name)))
    (asi-vigilant--record-source-file file)
    (cider-eval-region start end)))

;; Bind safe eval
(define-key cider-mode-map (kbd "C-c C-e") #'asi-cider-eval-region-safe)

;; ═══════════════════════════════════════════════════════════
;; 8. STARTUP HOOK
;; ═══════════════════════════════════════════════════════════

(add-hook 'cider-mode-hook
          (lambda ()
            (asi-vigilant-enable)
            (message "Vigilant CIDER activated for buffer %s" (current-buffer))))

(message "Vigilant CIDER loaded. Connect with: (cider-connect-clj '(:host \"localhost\" :port 1667))")
