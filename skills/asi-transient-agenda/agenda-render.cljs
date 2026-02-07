(ns asi-transient-agenda.agenda-render
  (:require ["child_process" :as cp]
            ["fs" :as fs]))

(defn emacsclient-eval [elisp]
  (cp/execSync (str "emacsclient --eval " (js/JSON.stringify elisp))
               #js {:encoding "utf-8" :maxBuffer (* 10 1024 1024)}))

(defn load-repo-data []
  (when (fs/existsSync "/tmp/asi-repos.el")
    (.trim (fs/readFileSync "/tmp/asi-repos.el" "utf-8"))))

(defn load-skill-data []
  (when (fs/existsSync "/tmp/asi-skills.el")
    (.trim (fs/readFileSync "/tmp/asi-skills.el" "utf-8"))))

(def hydra-elisp
  "(progn
     (require 'hydra)

     (defvar asi-agenda--repo-data nil)
     (defvar asi-agenda--skill-data nil)

     (defun asi-agenda--repo-count ()
       (if asi-agenda--repo-data
         (number-to-string (length asi-agenda--repo-data))
         \"?\"))

     (defun asi-agenda--skill-count ()
       (if asi-agenda--skill-data
         (number-to-string (length asi-agenda--skill-data))
         \"?\"))

     (defun asi-agenda-repos ()
       (interactive)
       (let ((buf (get-buffer-create \"*ASI Repos*\")))
         (with-current-buffer buf
           (read-only-mode -1)
           (erase-buffer)
           (insert \"#+TITLE: Plurigrid Repositories\\n\\n\")
           (dolist (entry asi-agenda--repo-data)
             (let ((lang (car entry))
                   (repos (cdr entry)))
               (insert (format \"** %s (%d repos)\\n\" lang (length repos)))
               (dolist (r repos)
                 (insert (format \"  - [[https://github.com/plurigrid/%s][%s]]\\n\" r r)))
               (insert \"\\n\")))
           (org-mode)
           (goto-char (point-min))
           (read-only-mode 1))
         (switch-to-buffer buf)))

     (defun asi-agenda-skills ()
       (interactive)
       (let ((buf (get-buffer-create \"*ASI Skills*\")))
         (with-current-buffer buf
           (read-only-mode -1)
           (erase-buffer)
           (insert \"#+TITLE: ASI Skills Dashboard\\n\\n\")
           (dolist (entry asi-agenda--skill-data)
             (insert (format \"  - [[file:/Users/bob/i/asi/skills/%s/SKILL.md][%s]] = %s\\n\"
                            (car entry) (car entry) (cdr entry))))
           (org-mode)
           (goto-char (point-min))
           (read-only-mode 1))
         (switch-to-buffer buf)))

     (defun asi-agenda-mcp ()
       (interactive)
       (async-shell-command \"bb -e '(println \\\"MCP: topos, mcp-tasks, babashka, nuworlds\\\")'\"))

     (defun asi-agenda-julia ()
       (interactive)
       (if (get-buffer \"*julia-repl*\")
         (switch-to-buffer \"*julia-repl*\")
         (ansi-term \"/Users/bob/.juliaup/bin/julia\" \"julia-repl\")))

     (defun asi-agenda-duckdb ()
       (interactive)
       (async-shell-command \"duckdb -c 'SELECT * FROM read_json_auto(\\\"/tmp/asi-repos.json\\\") LIMIT 10'\"))

     (defhydra asi-agenda (:color blue :hint nil :exit t)
       \"
 ASI Agenda: %s(asi-agenda--repo-count) repos | %s(asi-agenda--skill-count) skills
 -----------------------------------------------
  _r_ Repos        _s_ Skills      _m_ MCP
  _j_ Julia REPL   _d_ DuckDB      _t_ Triads
  _q_ Quit
\"
       (\"r\" asi-agenda-repos)
       (\"s\" asi-agenda-skills)
       (\"m\" asi-agenda-mcp)
       (\"j\" asi-agenda-julia)
       (\"d\" asi-agenda-duckdb)
       (\"t\" (message \"Triads: emacs(-1) + agenda(+1) + bb(0) = 0\"))
       (\"q\" nil))

     (global-set-key (kbd \"C-c a\") 'asi-agenda/body)
     (message \"ASI Agenda hydra loaded. C-c a to activate.\"))")

(defn -main []
  ;; Write a single elisp file that Emacs can load
  (let [repo-data  (load-repo-data)
        skill-data (load-skill-data)
        full-elisp (str "(progn\n"
                        (when repo-data
                          (str "  (setq asi-agenda--repo-data " repo-data ")\n"))
                        (when skill-data
                          (str "  (setq asi-agenda--skill-data " skill-data ")\n"))
                        ")\n")]
    ;; Write data + hydra definition to a file
    (fs/writeFileSync "/tmp/asi-agenda-init.el"
                      (str full-elisp "\n" hydra-elisp "\n")
                      "utf-8")
    ;; Load it via emacsclient
    (println (emacsclient-eval "(load-file \"/tmp/asi-agenda-init.el\")"))
    (println "ASI Agenda hydra installed in Emacs. Press C-c a to activate.")))

(-main)
