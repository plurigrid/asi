#!/usr/bin/env bb
;; alice-emacs-mods — one-shot daemon takeover (Babashka edition).
;; Canonical takeover (replaced takeover.sh 2026-04-21), plus prompt
;; suppression and seed-driven random grid ratio (2026-04-21).
(require '[babashka.fs :as fs]
         '[babashka.process :as p]
         '[clojure.string :as str])

(defn log [& xs] (binding [*out* *err*] (apply println "[bb]" xs) (flush)))

(def args *command-line-args*)
(def daemon  (nth args 0 "server"))
(def n-files (Integer/parseInt (nth args 1 "6")))
(def seed    (nth args 2 "0x42D"))
(def home    (System/getenv "HOME"))

(defn die [code & msg]
  (binding [*out* *err*] (apply println msg))
  (System/exit code))

(defn find-ec []
  ;; Shell glob first — recursive fs/glob over /nix/store hangs on ~45k entries.
  (or (let [{:keys [exit out]} (p/sh "bash" "-c" "ls /nix/store/*emacs-nox-*/bin/emacsclient 2>/dev/null | head -1")]
        (when (and (zero? exit) (not (str/blank? out))) (str/trim out)))
      (->> [(str home "/.nix-profile/bin/emacsclient")
            "/opt/homebrew/bin/emacsclient"
            "/usr/local/bin/emacsclient"]
           (filter fs/executable?) first)
      (let [{:keys [exit out]} (p/sh "bash" "-c" "command -v emacsclient")]
        (when (zero? exit) (str/trim out)))))

(def ec (or (find-ec) (die 2 "takeover: emacsclient not found")))
(log "ec=" ec)

(defn run-ec [form & {:keys [timeout-sec] :or {timeout-sec 5}}]
  (let [{:keys [exit out]} (p/sh "perl" "-e" "alarm shift; exec @ARGV"
                                 (str timeout-sec)
                                 ec "-s" daemon "-e" form)]
    (if (zero? exit) (str/trim (or out "")) ::timeout)))

(log "probing daemon" daemon)
(let [r (run-ec "(+ 1 1)" :timeout-sec 3)]
  (when-not (= r "2")
    (binding [*out* *err*]
      (println (str "takeover: daemon '" daemon "' not responsive (probe=" r ")"))
      (println "  available sockets:")
      (doseq [d (try (fs/glob "/var/folders" "*/*/T/emacs501/*")
                     (catch Exception _ []))]
        (println "   " (str d))))
    (System/exit 3)))

(defn recent-org-files [n]
  (let [roots (filter fs/exists?
                      [(str home "/worlds") (str home "/org")
                       (str home "/org-roam") (str home "/.emacs.d")])
        {:keys [out]} (apply p/sh "find" (concat roots
                       ["-maxdepth" "5" "-type" "f" "-name" "*.org"
                        "-not" "-path" "*/.git/*"
                        "-not" "-path" "*/elpa/*"
                        "-not" "-path" "*/node_modules/*"]))
        paths (->> (str/split (or out "") #"\n") (remove str/blank?))
        with-mtime (->> paths
                        (keep (fn [p]
                                (try [(.lastModified (java.io.File. p)) p]
                                     (catch Exception _ nil)))))]
    (->> with-mtime (sort-by first >) (map second) distinct (take n) vec)))

(log "probe ok; finding org files")
(def files (recent-org-files n-files))
(log "found" (count files) "files")
(when (empty? files)
  (die 4 "takeover: no .org files found in ~/worlds ~/org ~/org-roam ~/.emacs.d"))

;; --- seed-driven grid selection ---------------------------------------
;; Parse seed as unsigned hex, advance one SplitMix64-style step, mod by
;; the number of factor pairs of N. Same seed ⇒ same grid.

(defn seed->long [s]
  (Long/parseUnsignedLong (str/replace s #"^0[xX]" "") 16))

(def ^:const sm-golden -7046029254386353131) ; 0x9E3779B97F4A7C15
(def ^:const sm-mix1   -4658895280553007687) ; 0xBF58476D1CE4E5B9
(def ^:const sm-mix2   -7723592293110705685) ; 0x94D049BB133111EB

(defn splitmix64-step [state]
  (let [s (unchecked-add state sm-golden)
        z s
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 30)) sm-mix1)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 27)) sm-mix2)]
    (bit-xor z (unsigned-bit-shift-right z 31))))

(defn factor-pairs [n]
  (vec (for [r (range 1 (inc n))
             :let [c (quot n r)]
             :when (and (pos? c) (= n (* r c)) (or (and (> r 1) (> c 1)) (= n 1)))]
         [r c])))

(defn query-frame-dims []
  (let [r (run-ec "(list (frame-width) (frame-height))" :timeout-sec 3)]
    (if (= r :user/timeout)
      [80 24]
      (try (let [parsed (read-string r)]
             [(first parsed) (second parsed)])
           (catch Exception _ [80 24])))))
(def frame-dims (query-frame-dims))
(def frame-w (first frame-dims))
(def frame-h (second frame-dims))
(defn fits? [[r c]] (and (<= (* r 6) frame-h) (<= (* c 15) frame-w)))
(def grid
  (let [pairs (factor-pairs (count files))
        viable (or (seq (filter fits? pairs)) pairs)
        sv    (seed->long seed)
        draw  (splitmix64-step sv)
        idx   (Math/floorMod draw (long (count viable)))]
    (log "frame=" frame-w "x" frame-h "all-pairs=" (count pairs) "viable=" (count viable))
    (nth viable idx)))

(def rows (first grid))
(def cols (second grid))
(log "grid=" rows "x" cols "(chosen from" (count (factor-pairs (count files))) "factor pairs of" (count files) ")")

(def files-elisp
  (str "(list " (str/join " " (map pr-str files)) ")"))

;; Split into ROWS rows × COLS cols, prompt-suppressed.
(def split-form
  (str "(condition-case _cc_err (with-timeout (90 \"elisp-timeout\") (progn
  (let ((files " files-elisp ")
        (rows " rows ")
        (cols " cols ")
        (inhibit-message t)
        (enable-local-variables :safe)
        (large-file-warning-threshold nil)
        (find-file-suppress-same-file-warnings t)
        (vc-follow-symlinks t)
        (confirm-nonexistent-file-or-buffer nil))
    (cl-letf (((symbol-function 'y-or-n-p) (lambda (&rest _) nil))
              ((symbol-function 'yes-or-no-p) (lambda (&rest _) nil)))
      (dolist (fr (frame-list))
        (with-selected-frame fr
(select-window (frame-first-window))
          (delete-other-windows)
          (let ((row-wins (list (selected-window))))
            (dotimes (_ (1- rows))
              (let ((new (split-window (car (last row-wins)) nil 'below)))
                (setq row-wins (nconc row-wins (list new)))))
            (balance-windows)
            (let ((all-wins
                   (apply #'append
                          (mapcar (lambda (rw)
                                    (let ((cs (list rw)))
                                      (dotimes (_ (1- cols))
                                        (let ((new (split-window (car (last cs)) nil 'right)))
                                          (setq cs (nconc cs (list new)))))
                                      cs))
                                  row-wins))))
              (balance-windows)
              (cl-loop for w in all-wins for f in files
                       do (with-selected-window w
                            (set-window-buffer w (find-file-noselect f)))))))))
    (format \"placed %d files across %d frame(s) %d windows (grid %dx%d)\"
            (length files) (length (frame-list)) (length (window-list))
            rows cols)))) (error (format \"err=%S\" _cc_err)))"))

(log "running split-form (20s)")
(println (str "SPLIT: " (run-ec split-form :timeout-sec 180)))
(log "split done")

(def bridge (str home "/.claude/skills/emacs-strobe-walk/color-walk-gay.el"))
(def plain  (str home "/.claude/skills/emacs-strobe-walk/color-walk.el"))
(def walk   (or (when (fs/exists? bridge) bridge)
                (when (fs/exists? plain)  plain)))

(log "walk=" walk)
(when walk
  (println (str "LOAD: " walk))
  (run-ec (str "(load-file \"" walk "\")") :timeout-sec 10)
  (run-ec (str "(condition-case _cc_err (with-timeout (90 \"elisp-timeout\") (progn
  (when (fboundp 'horsin/enable) (horsin/enable))
  (setq horsin/seed " seed ")
  (when (boundp 'gay-seed) (setq gay-seed " seed "))
  (condition-case _ (horsin/reseed " seed ") (error (horsin/reseed))))")
          :timeout-sec 5))

(println (str "takeover: " daemon " <- " (count files) " files + color chain (seed " seed ") grid " rows "x" cols))
(doseq [[i f] (map-indexed vector files)]
  (printf "%6d\t%s%n" (inc i) f))
(println)
(println (str "attach:  " ec " -s " daemon " -t"))
