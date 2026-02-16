;;;; plr-thread-coloring/plr_thread.lisp
;;;; PLR Thread Coloring in Common Lisp with Sexp Representation
;;;; One-Hot Keyspace Reduction for Behavior Indexing

(defpackage #:plr-thread-coloring
  (:use #:cl)
  (:export #:thread-to-color
           #:P #:L #:R
           #:apply-plr-sequence
           #:behavior-class
           #:one-hot-to-gf3
           #:make-perception-action-field
           #:perceive!
           #:act!))

(in-package #:plr-thread-coloring)

;;; ============================================================
;;; SplitMix64 Constants
;;; ============================================================

(defconstant +golden+ #x9E3779B97F4A7C15)
(defconstant +mix1+ #xBF58476D1CE4E5B9)
(defconstant +mix2+ #x94D049BB133111EB)
(defconstant +mask64+ #xFFFFFFFFFFFFFFFF)
(defconstant +zubuyul+ 1069)

;;; ============================================================
;;; SplitMix64 PRNG
;;; ============================================================

(defun splitmix64 (seed)
  "SplitMix64 PRNG - deterministic and splittable."
  (declare (type (unsigned-byte 64) seed))
  (let* ((s (logand (+ seed +golden+) +mask64+))
         (z s)
         (z (logand (* (logxor z (ash z -30)) +mix1+) +mask64+))
         (z (logand (* (logxor z (ash z -27)) +mix2+) +mask64+)))
    (values s (logxor z (ash z -31)))))

(defun hue-to-trit (h)
  "Map hue (0-360) to GF(3) trit: -1, 0, +1."
  (let ((h (mod h 360)))
    (cond
      ((or (< h 60) (>= h 300)) 1)   ; PLUS (warm)
      ((< h 180) 0)                   ; ERGODIC (neutral)
      (t -1))))                       ; MINUS (cold)

;;; ============================================================
;;; Thread Color Structure
;;; ============================================================

(defstruct thread-color
  "Color derived from thread identifier."
  thread-id
  seed
  (L 50.0 :type single-float)
  (C 50.0 :type single-float)
  (H 180.0 :type single-float)
  (trit 0 :type (integer -1 1)))

(defun thread-color-role (tc)
  "Get role name from trit."
  (ecase (thread-color-trit tc)
    (-1 :minus)
    (0 :ergodic)
    (1 :plus)))

(defun thread-color-to-sexp (tc)
  "Export thread color as s-expression."
  `(thread-color
    :id ,(thread-color-thread-id tc)
    :L ,(thread-color-L tc)
    :C ,(thread-color-C tc)
    :H ,(thread-color-H tc)
    :trit ,(thread-color-trit tc)
    :role ,(thread-color-role tc)))

;;; ============================================================
;;; Thread ID to Color
;;; ============================================================

(defun parse-hex-substring (s start end)
  "Parse hexadecimal substring to integer."
  (parse-integer (subseq s start end) :radix 16))

(defun thread-to-color (thread-id)
  "Convert thread ID to its FIRST color.
   The first color IS the thread's identity."
  (let* (;; Clean UUID
         (clean (remove #\- (string-left-trim "T-" thread-id)))
         ;; Parse seed from first 16 hex chars
         (seed (if (>= (length clean) 16)
                   (parse-hex-substring clean 0 16)
                   (sxhash thread-id))))
    
    ;; SplitMix64 for deterministic value
    (multiple-value-bind (next-seed val) (splitmix64 seed)
      (declare (ignore next-seed))
      
      ;; Extract LCH components from 64-bit value
      (let* ((L-raw (logand val #xFFFF))
             (C-raw (logand (ash val -16) #xFFFF))
             (H-raw (logand (ash val -32) #xFFFF))
             (L (+ 10.0 (* 85.0 (/ L-raw 65535.0))))
             (C (* 100.0 (/ C-raw 65535.0)))
             (H (* 360.0 (/ H-raw 65535.0)))
             (trit (hue-to-trit H)))
        
        (make-thread-color
         :thread-id thread-id
         :seed seed
         :L (coerce L 'single-float)
         :C (coerce C 'single-float)
         :H (coerce H 'single-float)
         :trit trit)))))

;;; ============================================================
;;; PLR Operations
;;; ============================================================

(defun P (color &key (direction 1))
  "Parallel transformation: Hue ±15°.
   Preserves L and C (2/3 common tones).
   Op trit: 0 (ERGODIC)"
  (let* ((new-H (mod (+ (thread-color-H color) (* 15 direction)) 360.0))
         (new-trit (hue-to-trit new-H)))
    (make-thread-color
     :thread-id (thread-color-thread-id color)
     :seed (thread-color-seed color)
     :L (thread-color-L color)
     :C (thread-color-C color)
     :H (coerce new-H 'single-float)
     :trit new-trit)))

(defun L (color &key (direction 1))
  "Leading-tone transformation: Lightness ±10.
   Preserves C and H (2/3 common tones).
   Op trit: -1 (MINUS)"
  (let ((new-L (max 1.0 (min 99.0 (+ (thread-color-L color) (* 10 direction))))))
    (make-thread-color
     :thread-id (thread-color-thread-id color)
     :seed (thread-color-seed color)
     :L (coerce new-L 'single-float)
     :C (thread-color-C color)
     :H (thread-color-H color)
     :trit (thread-color-trit color))))

(defun R (color &key (direction 1))
  "Relative transformation: Chroma ±20, Hue ±30°.
   Largest shift (only L preserved).
   Op trit: +1 (PLUS)"
  (let* ((new-C (max 0.0 (min 150.0 (+ (thread-color-C color) (* 20 direction)))))
         (new-H (mod (+ (thread-color-H color) (* 30 direction)) 360.0))
         (new-trit (hue-to-trit new-H)))
    (make-thread-color
     :thread-id (thread-color-thread-id color)
     :seed (thread-color-seed color)
     :L (thread-color-L color)
     :C (coerce new-C 'single-float)
     :H (coerce new-H 'single-float)
     :trit new-trit)))

(defun apply-plr-sequence (color sequence)
  "Apply PLR sequence string, return color path as list."
  (let ((path (list color))
        (current color))
    (loop for op across (string-upcase sequence)
          do (setf current
                   (case op
                     (#\P (P current))
                     (#\L (L current))
                     (#\R (R current))
                     (t current)))
          do (push current path))
    (nreverse path)))

;;; ============================================================
;;; Behavior Classification (9-class)
;;; ============================================================

(defparameter *behavior-classes*
  #("L-MINUS: contract/validate"
    "L-ERGODIC: adjust/balance"
    "L-PLUS: brighten/expand"
    "P-MINUS: local-validate"
    "P-ERGODIC: local-explore"
    "P-PLUS: local-expand"
    "R-MINUS: simplify/reduce"
    "R-ERGODIC: modulate/shift"
    "R-PLUS: elaborate/generate"))

(defun plr-op-trit (op)
  "Get trit for PLR operation."
  (case (char-upcase (if (characterp op) op (char (string op) 0)))
    (#\L -1)
    (#\P 0)
    (#\R 1)
    (t 0)))

(defun behavior-class (color-trit op-trit)
  "Compute 9-class behavior index.
   Returns: (class-index class-name)"
  (let* ((op-idx (ecase op-trit (-1 0) (0 1) (1 2)))
         (trit-idx (ecase color-trit (-1 0) (0 1) (1 2)))
         (cls (+ (* op-idx 3) trit-idx)))
    (values cls (aref *behavior-classes* cls))))

;;; ============================================================
;;; One-Hot Reduction
;;; ============================================================

(defun one-hot-to-gf3 (one-hot-list)
  "Reduce one-hot encoding (128 bits) to GF(3) trit.
   
   Input: list of 0/1 bits (length 128)
   Output: -1, 0, or +1
   
   This is the key efficiency gain:
   - 2^128 possible states → 3 possible states
   - 128 bits → 1.58 bits"
  (let ((value 0))
    ;; Convert one-hot to integer
    (loop for bit in one-hot-list
          for i from 0
          do (when (= bit 1)
               (setf value (logior value (ash 1 i)))))
    
    ;; Hash to 64-bit seed
    (let ((seed (logand value +mask64+)))
      ;; SplitMix64
      (multiple-value-bind (next-seed val) (splitmix64 seed)
        (declare (ignore next-seed))
        ;; Extract hue and map to trit
        (let ((H (* 360.0 (/ (logand (ash val -32) #xFFFF) 65535.0))))
          (hue-to-trit H))))))

;;; ============================================================
;;; Perception/Action Field
;;; ============================================================

(defstruct perception-action-field
  "Growing information field through PLR navigation."
  (seed +zubuyul+ :type integer)
  (capacity 1.0 :type single-float)
  (plr-history nil :type list)
  (color-memory (make-hash-table :test 'equal) :type hash-table))

(defun perceive! (field thread-id)
  "User perceives thread as colored behavior.
   Returns perception result plist."
  (let ((color (thread-to-color thread-id)))
    ;; Store in memory
    (setf (gethash thread-id (perception-action-field-color-memory field)) color)
    
    ;; Expand capacity based on color diversity
    (let ((memory (perception-action-field-color-memory field)))
      (when (> (hash-table-count memory) 1)
        (let ((hues nil))
          (maphash (lambda (k v) 
                     (declare (ignore k))
                     (push (thread-color-H v) hues))
                   memory)
          ;; Simple diversity: range / 360
          (let* ((min-h (reduce #'min hues))
                 (max-h (reduce #'max hues))
                 (diversity (/ (- max-h min-h) 360.0)))
            (setf (perception-action-field-capacity field)
                  (* (perception-action-field-capacity field)
                     (+ 1.0 (* 0.02 diversity))))))))
    
    ;; Classify behavior
    (multiple-value-bind (cls name) (behavior-class (thread-color-trit color) 0)
      (list :thread-id thread-id
            :color (thread-color-to-sexp color)
            :trit (thread-color-trit color)
            :role (thread-color-role color)
            :behavior-class cls
            :behavior-name name
            :capacity (perception-action-field-capacity field)))))

(defun act! (field plr-op)
  "User action (PLR choice) expands field capacity.
   Returns new capacity."
  (push (char-upcase (if (characterp plr-op) plr-op (char (string plr-op) 0)))
        (perception-action-field-plr-history field))
  
  ;; Compute diversity of last 10 operations
  (let* ((recent (subseq (perception-action-field-plr-history field)
                         0 (min 10 (length (perception-action-field-plr-history field)))))
         (unique (remove-duplicates recent))
         (diversity (/ (length unique) 3.0)))
    
    ;; Expand capacity
    (setf (perception-action-field-capacity field)
          (* (perception-action-field-capacity field)
             (+ 1.0 (* 0.05 diversity))))
    
    (perception-action-field-capacity field)))

;;; ============================================================
;;; Sexp Export
;;; ============================================================

(defun plr-coloring-to-sexp (thread-id plr-sequence)
  "Generate complete sexp for PLR thread coloring."
  (let* ((first-color (thread-to-color thread-id))
         (path (apply-plr-sequence first-color plr-sequence))
         (trits (mapcar #'thread-color-trit path)))
    `(plr-thread-coloring
      :thread-id ,thread-id
      :seed ,(thread-color-seed first-color)
      :first-color ,(thread-color-to-sexp first-color)
      :plr-sequence ,plr-sequence
      :path ,(mapcar #'thread-color-to-sexp path)
      :gf3-sum ,(reduce #'+ trits)
      :gf3-conserved ,(zerop (mod (reduce #'+ trits) 3)))))

;;; ============================================================
;;; Demo
;;; ============================================================

(defun demo ()
  "Demonstrate PLR Thread Coloring."
  (format t "~%╔══════════════════════════════════════════════════════════════╗~%")
  (format t "║  PLR THREAD COLORING (Common Lisp)                           ║~%")
  (format t "║  One-Hot → GF(3) | Behavior Indexing | Sexp                  ║~%")
  (format t "╚══════════════════════════════════════════════════════════════╝~%~%")
  
  (let ((thread "T-019b77f9-2cae-7661-bf9f-714d9c5e677c"))
    ;; First color
    (format t "─── Thread → First Color ───~%")
    (let ((color (thread-to-color thread)))
      (format t "  Thread: ~A~%" thread)
      (format t "  L=~,1F C=~,1F H=~,1F~%" 
              (thread-color-L color)
              (thread-color-C color)
              (thread-color-H color))
      (format t "  Trit: ~D (~A)~%~%" 
              (thread-color-trit color)
              (thread-color-role color))
      
      ;; PLR path
      (format t "─── PLR Path ───~%")
      (let ((path (apply-plr-sequence color "PLR")))
        (loop for c in path
              for i from 0
              for op in '("•" "P" "L" "R")
              do (format t "  ~A: L=~,1F C=~,1F H=~,1F [~A]~%"
                         op
                         (thread-color-L c)
                         (thread-color-C c)
                         (thread-color-H c)
                         (thread-color-role c)))
        
        ;; GF(3) sum
        (let ((trits (mapcar #'thread-color-trit path)))
          (format t "~%  GF(3) sum: ~D (mod 3 = ~D)~%~%" 
                  (reduce #'+ trits)
                  (mod (reduce #'+ trits) 3))))
      
      ;; Behavior classes
      (format t "─── 9-Class Behavior Index ───~%")
      (dolist (op '("P" "L" "R"))
        (multiple-value-bind (cls name) 
            (behavior-class (thread-color-trit color) (plr-op-trit op))
          (format t "  ~A: class ~D → ~A~%" op cls name)))
      
      ;; One-hot reduction
      (format t "~%─── One-Hot Reduction ───~%")
      (let* ((one-hot (loop for i below 128 collect (if (= i 42) 1 0)))
             (trit (one-hot-to-gf3 one-hot)))
        (format t "  One-hot[42] (128 bits) → trit ~D~%" trit)
        (format t "  Reduction: 2^128 states → 3 states~%"))
      
      ;; Sexp export
      (format t "~%─── Sexp Export ───~%")
      (let ((sexp (plr-coloring-to-sexp thread "PLR")))
        (format t "  ~S~%" (subseq (prin1-to-string sexp) 0 100)))))
  
  (values))

;; (demo)
