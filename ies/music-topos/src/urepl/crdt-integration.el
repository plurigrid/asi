;;; CRDT-Aware Line Damage Formalization
;;; Integration with crdt.el for collaborative UREPL editing
;;; Handles character-level operations with conflict-free resolution
;;;
;;; Extends crdt.el with:
;;; 1. Operation tracking and metadata
;;; 2. Möbius inversion for conflict resolution
;;; 3. Prime factor extraction from operation IDs
;;; 4. Line damage visualization with Gay.jl colors

;; ============================================================================
;; CRDT Character Structure
;; ============================================================================

(cl-defstruct crdt-char
  "Character with CRDT metadata for collaborative editing"
  (value "" :type string)           ; The actual character
  (id nil :type (or string nil))    ; Unique identifier (site-id + lamport-clock)
  (site-id nil :type (or string nil))  ; Which agent inserted this
  (lamport-ts 0 :type integer)      ; Lamport timestamp for ordering
  (parent-id nil :type (or string nil))  ; Causal precedence
  (deleted nil :type boolean)       ; Tombstone for deletion
  (color nil :type (or string nil)) ; Gay.jl color for this operation
  (agent nil :type (or string nil)) ; Which agent (xenodium/batsov/xah-lee)
)

;; ============================================================================
;; CRDT Operation Structure
;; ============================================================================

(cl-defstruct crdt-operation
  "Operation for line modification with CRDT properties"
  (id nil :type string)             ; Operation UUID
  (type nil :type symbol)           ; 'insert, 'delete, 'update
  (char (make-crdt-char) :type crdt-char)
  (position 0 :type integer)        ; Position in document
  (timestamp nil :type (or null))   ; ISO-8601 timestamp
  (color nil :type (or string nil)) ; Color for visualization
  (agent-id nil :type (or string nil))  ; Which agent
  (proof-sketch nil :type (or string nil)))  ; For verification

;; ============================================================================
;; Line Damage Tracking
;; ============================================================================

(defun crdt-line-damage-formalize (line operations)
  "Formalize line damage tracking for collaborative editing"

  (let ((char-list (string-to-list line))
        (damage-map (make-hash-table :test 'equal)))

    ;; Track which positions were modified by which agents
    (dolist (op operations)
      (let* ((pos (crdt-operation-position op))
             (agent (crdt-operation-agent-id op))
             (color (crdt-operation-color op))
             (type (crdt-operation-type op)))

        ;; Record damage tuple: (agent color type timestamp)
        (puthash pos
                 (list agent color type (crdt-operation-timestamp op))
                 damage-map)))

    ;; Return line with damage annotations
    (list :line line
          :damage damage-map
          :char-count (length char-list)
          :operation-count (length operations)
          :chars
          (mapcar (lambda (c)
                    (make-crdt-char :value (string c)
                                   :deleted nil))
                  char-list))))

;; ============================================================================
;; Conflict Resolution via Möbius Inversion + Prime Filtering
;; ============================================================================

(defun crdt-extract-primes (id-string)
  "Extract prime factors from operation ID string"

  (let ((num (string-to-number id-string))
        (factors '()))

    ;; Factor the ID number using small primes
    (dolist (p '(2 3 5 7 11 13 17 19 23 29 31 37 41 43 47))
      (while (= (mod num p) 0)
        (push p factors)
        (setq num (/ num p))))

    (reverse factors)))

(defun crdt-moebius-function (prime-factors)
  "Calculate Möbius function value for conflict resolution"

  (let ((unique-primes (seq-uniq prime-factors)))
    (cond
      ;; All distinct primes: (-1)^k where k = count of primes
      ((= (length unique-primes) (length prime-factors))
       (if (= (mod (length prime-factors) 2) 0) 1 -1))

      ;; Any prime appears twice or more: return 0
      (t 0))))

(defun crdt-conflict-resolve (operations)
  "Resolve conflicts using Möbius inversion + prime filtering"

  ;; Extract prime factors from each operation's ID
  (let* ((op-signatures
          (mapcar (lambda (op)
                    (cons op (crdt-extract-primes (crdt-operation-id op))))
                  operations))

         ;; Calculate Möbius values for deterministic ordering
         (moebius-values
          (mapcar (lambda (sig)
                    (cons (car sig) (crdt-moebius-function (cdr sig))))
                  op-signatures)))

    ;; Sort by Möbius value (stable sort) then by Lamport timestamp
    (sort moebius-values
          (lambda (m1 m2)
            (let ((moeb1 (cdr m1))
                  (moeb2 (cdr m2))
                  (op1 (car m1))
                  (op2 (car m2)))

              (cond
                ;; Larger Möbius value comes first
                ((> moeb1 moeb2) t)
                ((< moeb1 moeb2) nil)

                ;; Same Möbius value: sort by lamport timestamp
                (t (< (crdt-char-lamport-ts (crdt-operation-char op1))
                      (crdt-char-lamport-ts (crdt-operation-char op2))))))))))

;; ============================================================================
;; Line Damage Visualization with Colors
;; ============================================================================

(defun crdt-visualize-damage (line-damage-info)
  "Visualize line damage with color annotations"

  (let* ((line (plist-get line-damage-info :line))
         (damage-map (plist-get line-damage-info :damage))
         (char-count (plist-get line-damage-info :char-count))
         (output ""))

    ;; Build annotated line with color codes
    (dotimes (i char-count)
      (let ((damage (gethash i damage-map)))
        (if damage
            ;; Position has damage: annotate with agent + color
            (let* ((agent (car damage))
                   (color (cadr damage))
                   (type (caddr damage)))
              (setq output (concat output
                                   (format "[%s:%s:%s]" agent color type))))
          ;; No damage: just output character
          (setq output (concat output (substring line i (1+ i)))))))

    output))

;; ============================================================================
;; Lamport Clock Management
;; ============================================================================

(defvar crdt-lamport-clock 0
  "Current Lamport clock value for this agent")

(defun crdt-increment-lamport ()
  "Increment Lamport clock"
  (setq crdt-lamport-clock (1+ crdt-lamport-clock)))

(defun crdt-update-lamport (received-ts)
  "Update Lamport clock based on received timestamp"
  (setq crdt-lamport-clock (max crdt-lamport-clock received-ts))
  (crdt-increment-lamport))

;; ============================================================================
;; Operation Generation
;; ============================================================================

(defun crdt-create-insert-op (position char agent-id color)
  "Create an insert operation"

  (crdt-increment-lamport)

  (make-crdt-operation
    :id (format "%s-%s-%d" agent-id (current-time-string) crdt-lamport-clock)
    :type 'insert
    :char (make-crdt-char
            :value (string char)
            :site-id agent-id
            :lamport-ts crdt-lamport-clock
            :color color
            :agent agent-id)
    :position position
    :timestamp (format-time-string "%Y-%m-%dT%H:%M:%S.%3NZ")
    :color color
    :agent-id agent-id))

(defun crdt-create-delete-op (position agent-id color)
  "Create a delete operation"

  (crdt-increment-lamport)

  (make-crdt-operation
    :id (format "%s-%s-%d" agent-id (current-time-string) crdt-lamport-clock)
    :type 'delete
    :position position
    :timestamp (format-time-string "%Y-%m-%dT%H:%M:%S.%3NZ")
    :color color
    :agent-id agent-id))

;; ============================================================================
;; Integration with crdt.el
;; ============================================================================

(defun crdt-after-change-hook (beg end len)
  "Hook into Emacs buffer changes for CRDT tracking"

  ;; This would be registered with add-hook for 'after-change-functions'
  (let* ((operation-type (cond
                          ((= len 0) 'insert)   ; Inserted text
                          ((> len 0) 'delete)))  ; Deleted text
         (agent-id (or (getenv "CRDT_AGENT_ID") "unknown"))
         (color (or (getenv "CRDT_COLOR") "#FF6B6B")))

    (cond
      ((eq operation-type 'insert)
       (let ((new-text (buffer-substring beg end)))
         (dolist (c (string-to-list new-text))
           (crdt-create-insert-op beg c agent-id color))))

      ((eq operation-type 'delete)
       (crdt-create-delete-op beg agent-id color)))))

;; ============================================================================
;; Proof Sketches for Operations
;; ============================================================================

(defun crdt-generate-proof-sketch (operation)
  "Generate a proof sketch for an operation"

  (let ((type (crdt-operation-type operation))
        (pos (crdt-operation-position operation))
        (char-val (crdt-char-value (crdt-operation-char operation))))

    (cond
      ((eq type 'insert)
       (format "insert(%s, %d, %s) → consistent" char-val pos (crdt-operation-agent-id operation)))

      ((eq type 'delete)
       (format "delete(%d, %s) → tombstone" pos (crdt-operation-agent-id operation)))

      (t "unknown"))))

;; ============================================================================
;; Test Functions
;; ============================================================================

(comment
  ;; Test line damage formalization
  (let ((ops (list
              (make-crdt-operation
                :id "agent1-1"
                :type 'insert
                :position 0
                :agent-id "agent1"
                :color "#FF6B6B")
              (make-crdt-operation
                :id "agent2-1"
                :type 'insert
                :position 1
                :agent-id "agent2"
                :color "#4ECDC4"))))
    (crdt-line-damage-formalize "hello" ops))

  ;; Test conflict resolution
  (let ((ops (list
              (make-crdt-operation
                :id "210"  ; 2 * 3 * 5 * 7
                :type 'insert)
              (make-crdt-operation
                :id "30"   ; 2 * 3 * 5
                :type 'insert))))
    (crdt-conflict-resolve ops))

  ;; Test prime extraction
  (crdt-extract-primes "210")  ; → (2 3 5 7)
  (crdt-moebius-function '(2 3 5 7))  ; → -1 (odd count)
)
