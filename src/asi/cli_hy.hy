;;; asi/cli.hy
;;; Algebraic Superintelligence - CLI in Hy
;;;
;;; Usage:
;;;   uvx asi          # Launch TUI or show skills
;;;   uvx asi skills   # List skills with GF(3)
;;;   uvx asi gf3      # Show GF(3) conservation
;;;   uvx asi info     # System info

(import click)
(import sys)
(import subprocess)
(import pathlib [Path])
(import rich.console [Console])
(import rich.table [Table])
(import rich.panel [Panel])

(import asi.core :as core)

(setv console (Console))

;; ═══════════════════════════════════════════════════════════════════════════════
;; SKILLS COMMAND
;; ═══════════════════════════════════════════════════════════════════════════════

(defn show-skills [trit-filter limit]
  "Display skills table with GF(3) annotations"
  (setv all-skills (core.load-skills))
  
  (when (is-not trit-filter None)
    (setv all-skills (lfor s all-skills 
                           :if (= (.get s "trit" 0) trit-filter) 
                           s)))
  
  (setv table (Table :title "ASI Skills (GF(3) Conservation)"))
  (.add-column table "Trit" :justify "center" :width 4)
  (.add-column table "Skill" :style "bold")
  (.add-column table "Description" :style "dim")
  
  (for [skill (cut all-skills 0 limit)]
    (setv t (.get skill "trit" 0))
    (.add-row table
              (core.trit-symbol t)
              (get skill "name")
              (cut (.get skill "description" "") 0 40)))
  
  (.print console table)
  
  ;; Show GF(3) summary
  (setv balance (core.gf3-balance all-skills))
  (.print console "")
  (.print console (Panel (core.format-gf3-status balance) :title "GF(3) Balance")))

;; ═══════════════════════════════════════════════════════════════════════════════
;; GF3 COMMAND
;; ═══════════════════════════════════════════════════════════════════════════════

(defn show-gf3 []
  "Show detailed GF(3) conservation status"
  (setv all-skills (core.load-skills))
  (setv balance (core.gf3-balance all-skills))
  
  (.print console (Panel.fit
    (+ "[bold]GF(3) Conservation Law[/]\n\n"
       "inject(+1) + bridge(0) + emit(-1) ≡ 0 (mod 3)\n\n"
       "Every operation must balance trits {-1, 0, +1}")
    :title "Bicomodule Framework"))
  (.print console "")
  
  ;; PLUS skills
  (setv plus-skills (lfor s all-skills :if (= (.get s "trit" 0) 1) s))
  (.print console "[bold green]PLUS (+1) - Generation/Synthesis[/]")
  (for [s (cut plus-skills 0 10)]
    (.print console (+ "  + " (get s "name"))))
  (when (> (len plus-skills) 10)
    (.print console (+ "  ... and " (str (- (len plus-skills) 10)) " more")))
  (.print console "")
  
  ;; ERGODIC skills
  (setv ergodic-skills (lfor s all-skills :if (= (.get s "trit" 0) 0) s))
  (.print console "[bold cyan]ERGODIC (0) - Coordination/Infrastructure[/]")
  (for [s (cut ergodic-skills 0 10)]
    (.print console (+ "  ○ " (get s "name"))))
  (when (> (len ergodic-skills) 10)
    (.print console (+ "  ... and " (str (- (len ergodic-skills) 10)) " more")))
  (.print console "")
  
  ;; MINUS skills
  (setv minus-skills (lfor s all-skills :if (= (.get s "trit" 0) -1) s))
  (.print console "[bold magenta]MINUS (-1) - Verification/Validation[/]")
  (for [s (cut minus-skills 0 10)]
    (.print console (+ "  − " (get s "name"))))
  (when (> (len minus-skills) 10)
    (.print console (+ "  ... and " (str (- (len minus-skills) 10)) " more")))
  (.print console "")
  
  ;; Summary panel
  (setv conserved-text (if (get balance "conserved")
                           "[green]✓ BALANCED[/]"
                           "[red]✗ UNBALANCED[/]"))
  (.print console (Panel
    (+ "Total: " (str (len all-skills)) " skills\n"
       "PLUS: " (str (get balance "plus")) " | ERGODIC: " (str (get balance "ergodic")) " | MINUS: " (str (get balance "minus")) "\n"
       "Sum: " (str (get balance "sum")) " ≡ " (str (get balance "mod3")) " (mod 3)\n"
       "Conservation: " conserved-text)
    :title "GF(3) Status")))

;; ═══════════════════════════════════════════════════════════════════════════════
;; INFO COMMAND
;; ═══════════════════════════════════════════════════════════════════════════════

(defn show-info []
  "Show system information"
  (.print console (Panel.fit
    (+ "[bold]Plurigrid ASI[/] v0.1.0\n\n"
       "Algebraic Superintelligence\n"
       "Category-theoretic skill framework\n"
       "Powered by [bold cyan]Hy[/] (Lisp on Python)\n\n"
       "Canonical Seed: " (str core.CANONICAL-SEED) "\n"
       "Skills Path: " (str (core.get-skills-dir)) "\n"
       "Root: " (str (core.get-asi-root)))
    :title "System Info")))

;; ═══════════════════════════════════════════════════════════════════════════════
;; MAIN - Simple argparse instead of Click decorators
;; ═══════════════════════════════════════════════════════════════════════════════

(defn main []
  "Main entry point"
  (import argparse)
  (setv parser (argparse.ArgumentParser :description "ASI - Algebraic Superintelligence"))
  (setv subparsers (.add-subparsers parser :dest "command"))
  
  ;; skills command
  (setv skills-parser (.add-parser subparsers "skills" :help "List skills with GF(3)"))
  (.add-argument skills-parser "--trit" "-t" :type int :default None :help "Filter by trit")
  (.add-argument skills-parser "--limit" "-n" :type int :default 50 :help "Limit results")
  
  ;; gf3 command
  (.add-parser subparsers "gf3" :help "Show GF(3) conservation status")
  
  ;; info command
  (.add-parser subparsers "info" :help "Show system information")
  
  (setv args (.parse-args parser))
  
  (cond
    (= args.command "skills")
    (show-skills args.trit args.limit)
    
    (= args.command "gf3")
    (show-gf3)
    
    (= args.command "info")
    (show-info)
    
    True
    (show-skills None 50)))

(when (= __name__ "__main__")
  (main))
