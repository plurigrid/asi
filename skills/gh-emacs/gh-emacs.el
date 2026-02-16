;;; gh-emacs.el --- Interactive GitHub CLI for Emacs -*- lexical-binding: t -*-

;; Author: bmorphism
;; Keywords: tools, vc, github
;; Package-Requires: ((emacs "29.1") (consult "1.0") (ghub "4.0") (forge "0.4"))

;;; Commentary:
;; Unified GitHub CLI integration combining consult-gh, forge, and ghub
;; with Gay.jl color streams and chatgpt-shell AI assistance.

;;; Code:

(require 'cl-lib)
(require 'json)

;;; Gay.jl Color Stream (Stream 3 - Bitter Lesson)

(defvar gh-emacs-colors
  ["#63B6F0" "#89DF91" "#CF6971" "#8E9EDF" "#C25828" "#ED6BDB" "#D1E598"]
  "GitHub state colors from Gay.jl stream 3.")

(defvar gh-emacs-state-colors
  '((open . "#89DF91")
    (closed . "#CF6971")
    (merged . "#8E9EDF")
    (draft . "#C25828")
    (review-required . "#ED6BDB")
    (approved . "#D1E598")
    (default . "#63B6F0"))
  "Map PR/issue states to colors.")

(defun gh-emacs-color-for-state (state)
  "Get color for STATE symbol."
  (or (alist-get state gh-emacs-state-colors)
      (alist-get 'default gh-emacs-state-colors)))

;;; gh CLI Wrapper Functions

(defun gh-emacs--run (args &optional callback)
  "Run gh CLI with ARGS. Call CALLBACK with result if provided."
  (let ((cmd (mapconcat #'shell-quote-argument (cons "gh" args) " ")))
    (if callback
        (make-process
         :name "gh-emacs"
         :command (cons "gh" args)
         :buffer "*gh-output*"
         :sentinel (lambda (proc _event)
                     (when (eq (process-status proc) 'exit)
                       (with-current-buffer (process-buffer proc)
                         (funcall callback (buffer-string))))))
      (shell-command-to-string cmd))))

(defun gh-emacs--json (args)
  "Run gh CLI with ARGS, parse JSON output."
  (let ((result (gh-emacs--run (append args '("--json")))))
    (condition-case nil
        (json-read-from-string result)
      (error nil))))

;;; Interactive Commands

;;;###autoload
(defun gh-emacs-search-repos (query)
  "Search GitHub repos for QUERY."
  (interactive "sSearch repos: ")
  (let* ((results (gh-emacs--run 
                   (list "search" "repos" query "--limit" "20" "--json" 
                         "fullName,description,stargazersCount")))
         (repos (json-read-from-string results)))
    (with-current-buffer (get-buffer-create "*gh-repos*")
      (erase-buffer)
      (insert "# GitHub Repository Search: " query "\n\n")
      (seq-doseq (repo repos)
        (let ((name (alist-get 'fullName repo))
              (desc (or (alist-get 'description repo) ""))
              (stars (alist-get 'stargazersCount repo)))
          (insert (format "- **%s** ⭐%d\n  %s\n\n" name stars desc))))
      (goto-char (point-min))
      (when (fboundp 'gfm-mode) (gfm-mode))
      (pop-to-buffer (current-buffer)))))

;;;###autoload
(defun gh-emacs-pr-list ()
  "List PRs for current repository."
  (interactive)
  (let* ((results (gh-emacs--run 
                   '("pr" "list" "--json" "number,title,state,author")))
         (prs (json-read-from-string results)))
    (with-current-buffer (get-buffer-create "*gh-prs*")
      (erase-buffer)
      (insert "# Pull Requests\n\n")
      (seq-doseq (pr prs)
        (let* ((num (alist-get 'number pr))
               (title (alist-get 'title pr))
               (state (intern (alist-get 'state pr)))
               (author (alist-get 'login (alist-get 'author pr)))
               (color (gh-emacs-color-for-state state)))
          (insert (propertize (format "#%d" num) 'face `(:foreground ,color :weight bold))
                  (format " %s (@%s)\n" title author))))
      (goto-char (point-min))
      (pop-to-buffer (current-buffer)))))

;;;###autoload
(defun gh-emacs-issue-list ()
  "List issues for current repository."
  (interactive)
  (let* ((results (gh-emacs--run 
                   '("issue" "list" "--json" "number,title,state,labels")))
         (issues (json-read-from-string results)))
    (with-current-buffer (get-buffer-create "*gh-issues*")
      (erase-buffer)
      (insert "# Issues\n\n")
      (seq-doseq (issue issues)
        (let* ((num (alist-get 'number issue))
               (title (alist-get 'title issue))
               (state (intern (alist-get 'state issue)))
               (color (gh-emacs-color-for-state state)))
          (insert (propertize (format "#%d" num) 'face `(:foreground ,color :weight bold))
                  (format " %s\n" title))))
      (goto-char (point-min))
      (pop-to-buffer (current-buffer)))))

;;;###autoload
(defun gh-emacs-clone (repo)
  "Clone REPO to default directory."
  (interactive "sRepository (owner/repo): ")
  (let ((dir (expand-file-name repo "~/src/")))
    (gh-emacs--run (list "repo" "clone" repo dir))
    (when (file-directory-p dir)
      (dired dir))))

;;;###autoload
(defun gh-emacs-view-pr-diff (number)
  "View diff for PR NUMBER."
  (interactive "nPR number: ")
  (let ((diff (gh-emacs--run (list "pr" "diff" (number-to-string number)))))
    (with-current-buffer (get-buffer-create "*gh-pr-diff*")
      (erase-buffer)
      (insert diff)
      (diff-mode)
      (goto-char (point-min))
      (pop-to-buffer (current-buffer)))))

;;;###autoload
(defun gh-emacs-run-list ()
  "List workflow runs."
  (interactive)
  (let* ((results (gh-emacs--run 
                   '("run" "list" "--json" "databaseId,displayTitle,status,conclusion")))
         (runs (json-read-from-string results)))
    (with-current-buffer (get-buffer-create "*gh-runs*")
      (erase-buffer)
      (insert "# Workflow Runs\n\n")
      (seq-doseq (run runs)
        (let* ((id (alist-get 'databaseId run))
               (title (alist-get 'displayTitle run))
               (status (alist-get 'status run))
               (conclusion (alist-get 'conclusion run))
               (color (cond
                       ((string= conclusion "success") "#89DF91")
                       ((string= conclusion "failure") "#CF6971")
                       ((string= status "in_progress") "#ED6BDB")
                       (t "#63B6F0"))))
          (insert (propertize (format "%s" id) 'face `(:foreground ,color))
                  (format " %s [%s]\n" title (or conclusion status)))))
      (goto-char (point-min))
      (pop-to-buffer (current-buffer)))))

;;; AI Integration (requires chatgpt-shell)

(declare-function chatgpt-shell-send-to-buffer "chatgpt-shell" (text))

;;;###autoload
(defun gh-emacs-ai-review-pr (number)
  "Use AI to review PR NUMBER."
  (interactive "nPR number: ")
  (when (require 'chatgpt-shell nil t)
    (let* ((diff (gh-emacs--run (list "pr" "diff" (number-to-string number))))
           (prompt (format "Review this pull request diff for:
1. Potential bugs or issues
2. Code style improvements  
3. Security concerns
4. Performance implications

```diff
%s
```" (substring diff 0 (min 8000 (length diff))))))
      (chatgpt-shell-send-to-buffer prompt))))

;;;###autoload
(defun gh-emacs-ai-generate-description ()
  "Generate PR description from staged changes using AI."
  (interactive)
  (when (require 'chatgpt-shell nil t)
    (let* ((diff (shell-command-to-string "git diff --staged"))
           (prompt (format "Generate a clear PR description:

```diff
%s
```

Format: Title, Summary, Key Changes (bullets), Testing Notes"
                           (substring diff 0 (min 6000 (length diff))))))
      (chatgpt-shell-send-to-buffer prompt))))

;;; Transient Interface

(require 'transient nil t)

(when (featurep 'transient)
  (transient-define-prefix gh-emacs-transient ()
    "GitHub CLI interactive commands."
    ["Search"
     ("s r" "Repos" gh-emacs-search-repos)
     ("s c" "Code (consult)" consult-gh-search-code :if (lambda () (fboundp 'consult-gh-search-code)))]
    ["Current Repo"
     ("p l" "PR list" gh-emacs-pr-list)
     ("i l" "Issue list" gh-emacs-issue-list)
     ("r l" "Run list" gh-emacs-run-list)
     ("p d" "PR diff" gh-emacs-view-pr-diff)]
    ["Actions"
     ("c" "Clone" gh-emacs-clone)
     ("b" "Browse" (lambda () (interactive) (gh-emacs--run '("repo" "view" "--web"))))]
    ["AI (chatgpt-shell)"
     ("a r" "Review PR" gh-emacs-ai-review-pr :if (lambda () (fboundp 'chatgpt-shell-send-to-buffer)))
     ("a d" "Generate description" gh-emacs-ai-generate-description :if (lambda () (fboundp 'chatgpt-shell-send-to-buffer)))])
  
  (global-set-key (kbd "C-c g h") 'gh-emacs-transient))

(provide 'gh-emacs)
;;; gh-emacs.el ends here
