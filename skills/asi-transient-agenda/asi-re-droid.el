;; asi-re-droid-emacs.el — Reverse Engineering + Factory Droid patterns for Emacs TUI
;; Integrates: blackhat-go (186 techniques), radare2 MCP, Trail of Bits RE, Droid architecture
;;
;; Best of Factory Droid ported to Emacs:
;;   1. Skills = SKILL.md files → hydra dispatch (already have)
;;   2. Custom Droids = subagent orchestration → comint + MCP
;;   3. Headless exec = non-interactive analysis → async shell
;;   4. Context compression = incremental summarization → buffer-local summaries
;;   5. Mixed models = tool routing → radare2 for RE, bb for scripting

;; ═══════════════════════════════════════════════
;; 1. Radare2 MCP integration
;; ═══════════════════════════════════════════════

(defvar asi-re--r2-sessions '()
  "Active radare2 MCP sessions as alist of (name . session-id).")

(defvar asi-re--current-binary nil
  "Currently loaded binary path.")

(defun asi-re-open (path)
  "Open a binary in radare2 for analysis."
  (interactive "fBinary: ")
  (setq asi-re--current-binary (expand-file-name path))
  (let ((output (shell-command-to-string
                 (format "r2 -q -c 'iI' '%s' 2>/dev/null" asi-re--current-binary))))
    (asi-re--display "Binary Info" output)
    (message "Loaded: %s" (file-name-nondirectory path))))

(defun asi-re-functions ()
  "List functions in current binary."
  (interactive)
  (when asi-re--current-binary
    (let ((output (shell-command-to-string
                   (format "r2 -q -c 'aaa; afl' '%s' 2>/dev/null" asi-re--current-binary))))
      (asi-re--display "Functions" output))))

(defun asi-re-decompile (func)
  "Decompile a function using r2ghidra."
  (interactive "sFunction name (or address): ")
  (when asi-re--current-binary
    (let ((output (shell-command-to-string
                   (format "r2 -q -c 'aaa; s %s; pdg' '%s' 2>/dev/null"
                           func asi-re--current-binary))))
      (asi-re--display (format "Decompile: %s" func) output))))

(defun asi-re-strings ()
  "Extract strings from current binary."
  (interactive)
  (when asi-re--current-binary
    (let ((output (shell-command-to-string
                   (format "r2 -q -c 'izz~[3:]' '%s' 2>/dev/null | head -100"
                           asi-re--current-binary))))
      (asi-re--display "Strings (first 100)" output))))

(defun asi-re-sections ()
  "Show binary sections."
  (interactive)
  (when asi-re--current-binary
    (let ((output (shell-command-to-string
                   (format "r2 -q -c 'iS' '%s' 2>/dev/null" asi-re--current-binary))))
      (asi-re--display "Sections" output))))

(defun asi-re-imports ()
  "Show imports."
  (interactive)
  (when asi-re--current-binary
    (let ((output (shell-command-to-string
                   (format "r2 -q -c 'ii' '%s' 2>/dev/null" asi-re--current-binary))))
      (asi-re--display "Imports" output))))

(defun asi-re-xrefs (addr)
  "Show cross-references to address."
  (interactive "sAddress or symbol: ")
  (when asi-re--current-binary
    (let ((output (shell-command-to-string
                   (format "r2 -q -c 'aaa; axt @%s' '%s' 2>/dev/null"
                           addr asi-re--current-binary))))
      (asi-re--display (format "Xrefs to %s" addr) output))))

(defun asi-re-disasm (addr &optional count)
  "Disassemble at address."
  (interactive "sAddress: ")
  (when asi-re--current-binary
    (let ((n (or count 32))
          (output (shell-command-to-string
                   (format "r2 -q -c 'aaa; s %s; pd %d' '%s' 2>/dev/null"
                           addr n asi-re--current-binary))))
      (asi-re--display (format "Disasm @ %s" addr) output))))

(defun asi-re-cmd (cmd)
  "Run arbitrary r2 command on current binary."
  (interactive "sr2 command: ")
  (when asi-re--current-binary
    (let ((output (shell-command-to-string
                   (format "r2 -q -c 'aaa; %s' '%s' 2>/dev/null"
                           cmd asi-re--current-binary))))
      (asi-re--display (format "r2> %s" cmd) output))))

;; ═══════════════════════════════════════════════
;; 2. BlackHat-Go technique browser
;; ═══════════════════════════════════════════════

(defvar asi-re--bhg-categories
  '(("Foundation" . (1))
    ("Network" . (2 5 6))
    ("Web" . (3 4))
    ("Exploitation" . (9))
    ("Crypto" . (11))
    ("Windows" . (12))
    ("Evasion" . (13 14))
    ("macOS" . (15 16 17 18 19 20 21 22 23 24))
    ("Cloud" . (25))
    ("Mobile" . (26))
    ("IoT" . (27))
    ("SupplyChain" . (28))
    ("API" . (29))
    ("Web3" . (30))
    ("AI" . (31 37))
    ("RedTeam" . (32))
    ("Recon" . (33))
    ("ResourceDev" . (34))
    ("Collection" . (35))
    ("LateralMov" . (36)))
  "BlackHat-Go chapter categories.")

(defvar asi-re--bhg-high-risk
  '(("cicd-injection" "Ch.28" 10 "SupplyChain")
    ("smart-contract-reentrancy" "Ch.30" 10 "Web3")
    ("flash-loan-exploit" "Ch.30" 10 "Web3")
    ("private-key-extract" "Ch.30" 10 "Web3")
    ("k8s-pod-escape" "Ch.25" 10 "Cloud")
    ("process-injection" "Ch.12" 10 "Windows")
    ("rat-implant" "Ch.14" 10 "Evasion")
    ("dependency-confusion" "Ch.28" 9 "SupplyChain")
    ("oauth-token-theft" "Ch.29" 9 "API")
    ("wallet-drainer" "Ch.30" 9 "Web3")
    ("model-poisoning" "Ch.31" 9 "AI")
    ("rag-poisoning" "Ch.37" 9 "AI"))
  "High-risk techniques from blackhat-go (risk >= 9).")

(defvar asi-re--bhg-defenses
  '(("Hardware Wallet" 95 "private-key-extract, wallet-drainer")
    ("MFA" 95 "credential-harvester, pass-the-hash")
    ("SIP Enabled" 95 "nvram-persist, dyld-injection")
    ("IMDSv2" 90 "aws-metadata-ssrf, cloud-cred-harvest")
    ("JWT Validation" 90 "jwt-none-alg, oauth-token-theft")
    ("Zero Trust" 85 "remote-services, session-hijacking")
    ("EDR" 85 "process-injection, rat-implant")
    ("Smart Contract Audit" 85 "reentrancy, flash-loan-exploit")
    ("CI/CD Hardening" 85 "cicd-injection, build-artifact-poison")
    ("SBOM Verification" 80 "dependency-confusion, typosquatting")
    ("RAG Guardrails" 75 "rag-poisoning, vector-embedding-attack"))
  "Defense effectiveness from blackhat-go.")

(defun asi-re-bhg-threats ()
  "Display high-risk blackhat-go techniques in a colored buffer."
  (interactive)
  (let ((buf (get-buffer-create "*BHG Threats*")))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert (propertize "BlackHat-Go: High Risk Techniques (Risk >= 9)\n"
                            'face '(:height 1.4 :weight bold)))
        (insert (propertize "────────────────────────────────────────────\n"
                            'face '(:foreground "#555")))
        (dolist (tech asi-re--bhg-high-risk)
          (let* ((name (nth 0 tech))
                 (ch (nth 1 tech))
                 (risk (nth 2 tech))
                 (cat (nth 3 tech))
                 (risk-color (cond ((= risk 10) "#ff0000")
                                   ((= risk 9) "#ff6600")
                                   (t "#ffcc00"))))
            (insert (propertize (format "  RISK %d " risk)
                                'face `(:background ,risk-color :foreground "black" :weight bold))
                    " "
                    (propertize name 'face '(:weight bold))
                    (propertize (format "  %s  %s\n" ch cat) 'face '(:foreground "#888")))))
        (insert "\n" (propertize "Defenses\n" 'face '(:height 1.2 :weight bold)))
        (insert (propertize "────────────────────────────────────────────\n"
                            'face '(:foreground "#555")))
        (dolist (def asi-re--bhg-defenses)
          (let* ((name (nth 0 def))
                 (eff (nth 1 def))
                 (mitigates (nth 2 def))
                 (eff-color (cond ((>= eff 90) "#00cc00")
                                  ((>= eff 80) "#88cc00")
                                  (t "#cccc00"))))
            (insert (propertize (format "  %d%% " eff)
                                'face `(:foreground ,eff-color :weight bold))
                    (propertize name 'face '(:weight bold))
                    (propertize (format "  → %s\n" mitigates) 'face '(:foreground "#888")))))
        (goto-char (point-min))
        (special-mode)))
    (display-buffer buf)))

(defun asi-re-bhg-categories ()
  "Show blackhat-go categories overview."
  (interactive)
  (let ((buf (get-buffer-create "*BHG Categories*")))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert (propertize "BlackHat-Go: 186 Techniques across 37 Chapters\n"
                            'face '(:height 1.4 :weight bold)))
        (dolist (cat asi-re--bhg-categories)
          (let* ((name (car cat))
                 (chs (cdr cat))
                 (color (nth (mod (sxhash name) 24)
                             '("#769c7d" "#55b0e6" "#c8a0c2" "#ffa6c2" "#789a20" "#54c1ed"
                               "#285dd0" "#6233ef" "#d4be57" "#389bc3" "#7278c0" "#5fa42b"
                               "#c3f7fa" "#de1fbe" "#ec6698" "#b81660" "#49b0f2" "#50a9e3"
                               "#6fc6f9" "#7d13cb" "#5fb501" "#636fa4" "#5b63de" "#58e0a8"))))
            (insert (propertize (format "  %-14s" name) 'face `(:foreground ,color :weight bold))
                    (propertize (format " Ch.%s\n"
                                       (mapconcat #'number-to-string chs ","))
                                'face '(:foreground "#888")))))
        (goto-char (point-min))
        (special-mode)))
    (display-buffer buf)))

;; ═══════════════════════════════════════════════
;; 3. Trail of Bits skill integration
;; ═══════════════════════════════════════════════

(defvar asi-re--tob-skills
  '(;; Tier 1: Core 9 (OCAPN MVP)
    ("triadic-skill-orchestrator" 0 "Meta-coordinator")
    ("gf3-tripartite" 0 "GF(3) constraint")
    ("captp" 0 "Capability transfer")
    ("universal-captp-derivation" 0 "Derivation chains")
    ("skill-dispatch" 1 "Token generation")
    ("skill-connectivity-hub" 0 "Holder tracking")
    ("skill-bonds" -1 "Revocation")
    ("gf3-pr-verify" 0 "Verification")
    ("constant-time-analysis" 0 "Timing protection")
    ;; Tier 2: Security extensions
    ("blackhat-go" 1 "Threat vectors")
    ("constant-time-testing" 0 "Timing validation")
    ("consensus" 0 "Three-agent auth")
    ("bisimulation-game" 0 "Game verification")
    ("audit-context-building" 0 "Audit trails")
    ;; RE-specific
    ("radare2-hatchery" -1 "Binary analysis MCP")
    ("r2frida" 0 "Dynamic instrumentation")
    ("boxxy-reverse-engineering" 0 "Firmware extraction")
    ("dwarf-expert" 0 "DWARF debug info")
    ("semgrep" 0 "Static analysis patterns")
    ("codeql" 0 "Variant analysis"))
  "Trail of Bits skill topology for RE augmentation.")

(defun asi-re-tob-skills ()
  "Display Trail of Bits skill topology."
  (interactive)
  (let ((buf (get-buffer-create "*ToB Skills*")))
    (with-current-buffer buf
      (let ((inhibit-read-only t)
            (gf3-sum 0))
        (erase-buffer)
        (insert (propertize "Trail of Bits: Skill Topology for RE\n"
                            'face '(:height 1.4 :weight bold)))
        (insert (propertize "────────────────────────────────────────────\n"
                            'face '(:foreground "#555")))
        (dolist (skill asi-re--tob-skills)
          (let* ((name (nth 0 skill))
                 (trit (nth 1 skill))
                 (desc (nth 2 skill))
                 (trit-color (cond ((= trit 1) "#D82626")
                                   ((= trit -1) "#2626D8")
                                   (t "#26D826")))
                 (trit-sym (cond ((= trit 1) "+1")
                                 ((= trit -1) "-1")
                                 (t " 0"))))
            (setq gf3-sum (+ gf3-sum trit))
            (insert (propertize (format "  [%s] " trit-sym)
                                'face `(:foreground ,trit-color :weight bold))
                    (propertize (format "%-30s" name) 'face '(:weight bold))
                    (propertize desc 'face '(:foreground "#888"))
                    "\n")))
        (insert "\n"
                (propertize (format "GF(3) Sum: %d ≡ %d (mod 3) %s\n"
                                    gf3-sum (mod gf3-sum 3)
                                    (if (= 0 (mod gf3-sum 3)) "BALANCED" "UNBALANCED"))
                            'face `(:weight bold
                                    :foreground ,(if (= 0 (mod gf3-sum 3)) "#26D826" "#D82626"))))
        (goto-char (point-min))
        (special-mode)))
    (display-buffer buf)))

;; ═══════════════════════════════════════════════
;; 4. Droid-like headless exec (async shell analysis)
;; ═══════════════════════════════════════════════

(defun asi-re-exec (cmd &optional name)
  "Run an analysis command asynchronously (Droid headless exec pattern).
Returns buffer with live output."
  (let* ((buf-name (or name (format "*re-exec: %s*" (truncate-string-to-width cmd 40))))
         (buf (get-buffer-create buf-name)))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert (propertize (format "Executing: %s\n" cmd)
                            'face '(:foreground "#888" :slant italic)))
        (insert (propertize "────────────────────────────────────────────\n"
                            'face '(:foreground "#555")))))
    (start-process-shell-command buf-name buf cmd)
    (display-buffer buf)
    buf))

(defun asi-re-exec-r2 (r2-cmd)
  "Headless r2 command on current binary."
  (interactive "sr2 command (headless): ")
  (when asi-re--current-binary
    (asi-re-exec
     (format "r2 -q -c 'aaa; %s' '%s' 2>/dev/null" r2-cmd asi-re--current-binary)
     (format "*r2: %s*" r2-cmd))))

;; ═══════════════════════════════════════════════
;; 5. Display engine
;; ═══════════════════════════════════════════════

(defun asi-re--display (title content)
  "Display analysis result in a dedicated buffer with color."
  (let ((buf (get-buffer-create (format "*RE: %s*" title))))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert (propertize (concat title "\n") 'face '(:height 1.3 :weight bold)))
        (when asi-re--current-binary
          (insert (propertize (format "Binary: %s\n"
                                      (file-name-nondirectory asi-re--current-binary))
                              'face '(:foreground "#888"))))
        (insert (propertize "────────────────────────────────────────────\n"
                            'face '(:foreground "#555")))
        (insert content)
        (goto-char (point-min))
        (special-mode)))
    (display-buffer buf)))

;; ═══════════════════════════════════════════════
;; 6. Hydra — the unified RE + Droid interface
;; ═══════════════════════════════════════════════

(defhydra asi-re-hydra (:color blue :hint nil :exit t)
  "
 RE + Droid: %(if asi-re--current-binary (file-name-nondirectory asi-re--current-binary) \"no binary\")
 ────────────────────────────────────────────────
  radare2:  _o_ open   _f_ functions  _d_ decompile  _s_ strings
            _S_ sections  _i_ imports  _x_ xrefs  _D_ disasm
            _!_ r2 cmd    _h_ headless
  bhg:      _t_ threats   _c_ categories
  tob:      _T_ skill topology
  exec:     _e_ shell exec (async)
  _q_ quit
"
  ("o" asi-re-open)
  ("f" asi-re-functions)
  ("d" (call-interactively #'asi-re-decompile))
  ("s" asi-re-strings)
  ("S" asi-re-sections)
  ("i" asi-re-imports)
  ("x" (call-interactively #'asi-re-xrefs))
  ("D" (call-interactively #'asi-re-disasm))
  ("!" (call-interactively #'asi-re-cmd))
  ("h" (call-interactively #'asi-re-exec-r2))
  ("t" asi-re-bhg-threats)
  ("c" asi-re-bhg-categories)
  ("T" asi-re-tob-skills)
  ("e" (let ((cmd (read-string "Shell command: ")))
         (asi-re-exec cmd)))
  ("q" nil))

;; Wire into ASI agenda
(defun asi-agenda-re ()
  "Open RE + Droid hydra."
  (interactive)
  (asi-re-hydra/body))

;; Rebuild main agenda with RE key
(defhydra asi-agenda (:color blue :hint nil :exit t)
  "
 ASI Agenda: %(asi-agenda--repo-count) repos | %(asi-agenda--skill-count) skills
 ────────────────────────────────────────────────
  _r_ Repos     _s_ Skills    _m_ MCP      _d_ DuckDB
  _j_ Julia     _c_ Colors    _k_ Kaleidoscope
  _x_ TeX/xy-pic              _t_ Triads
  _o_ OCR->ACSet  _R_ RE+Droid _q_ Quit
"
  ("r" asi-agenda-repos)
  ("s" asi-agenda-skills)
  ("m" asi-agenda-mcp)
  ("j" asi-agenda-julia)
  ("d" asi-agenda-duckdb)
  ("c" asi-agenda-colors)
  ("k" asi-agenda-kaleidoscope)
  ("x" asi-agenda-tex)
  ("o" asi-agenda-ocr)
  ("R" asi-agenda-re)
  ("t" (message "Triads: emacs(-1) + agenda(+1) + bb(0) = 0"))
  ("q" nil))

(global-set-key (kbd "C-c a") 'asi-agenda/body)
(global-set-key (kbd "C-c r") 'asi-re-hydra/body)

(message "RE+Droid loaded. C-c r for RE hydra, C-c a R from agenda. 186 BHG techniques, 20 ToB skills, r2 integration.")
