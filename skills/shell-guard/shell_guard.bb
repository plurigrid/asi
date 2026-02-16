#!/usr/bin/env bb
(ns shell-guard
  (:require [babashka.process :as p]
            [babashka.fs :as fs]
            [clojure.string :as str]))

;; ═══════════════════════════════════════════════════════════════
;; SHELL DETECTION
;; ═══════════════════════════════════════════════════════════════

(def SHELL-PREFERENCE
  ["/bin/zsh"
   "/bin/bash"
   "/bin/sh"
   "/usr/bin/env"])

(defn find-shell []
  (or (first (filter #(and % (fs/exists? %) (fs/executable? %)) SHELL-PREFERENCE))
      (System/getenv "SHELL")))

(defn shell-info []
  {:found (find-shell)
   :env-shell (System/getenv "SHELL")
   :user (System/getenv "USER")
   :home (System/getenv "HOME")})

;; ═══════════════════════════════════════════════════════════════
;; ENVIRONMENT VALIDATION
;; ═══════════════════════════════════════════════════════════════

(defn which [cmd]
  (try
    (let [result (p/shell {:out :string :err :string :continue true} "which" cmd)]
      (when (zero? (:exit result))
        (str/trim (:out result))))
    (catch Exception _ nil)))

(defn validate-env [required-cmds]
  (let [results (map (fn [cmd] {:cmd cmd :path (which cmd)}) required-cmds)
        missing (filter #(nil? (:path %)) results)]
    {:valid (empty? missing)
     :missing (map :cmd missing)
     :found (filter :path results)}))

;; ═══════════════════════════════════════════════════════════════
;; SAFE SHELL EXECUTION
;; ═══════════════════════════════════════════════════════════════

(defn safe-shell
  [cmd & {:keys [cwd timeout env out err]
          :or {timeout 60000 out :string err :string}}]
  (let [shell (find-shell)
        opts (cond-> {:out out :err err :continue true}
               cwd (assoc :dir cwd)
               timeout (assoc :timeout timeout)
               env (assoc :extra-env env))]
    
    (when-not shell
      (throw (ex-info "No shell found" {:tried SHELL-PREFERENCE})))
    
    (try
      (p/shell opts shell "-c" cmd)
      (catch Exception e
        (let [msg (str e)]
          (if (str/includes? msg "ENOENT")
            (do
              (println "⚠️ Shell ENOENT, trying /bin/sh...")
              (try
                (p/shell opts "/bin/sh" "-c" cmd)
                (catch Exception _
                  (println "⚠️ Trying python3 fallback...")
                  (let [py-cmd (format "import subprocess; subprocess.run(['sh', '-c', '''%s'''], check=True)"
                                       (str/replace cmd "'" "\\'"))]
                    (p/shell opts "python3" "-c" py-cmd)))))
            (throw e)))))))

;; ═══════════════════════════════════════════════════════════════
;; FLOX INTEGRATION
;; ═══════════════════════════════════════════════════════════════

(defn with-flox [cmd & opts]
  (apply safe-shell (str "flox activate -- " cmd) opts))

(defn ensure-flox-env [required-cmds]
  (let [validation (validate-env required-cmds)]
    (if (:valid validation)
      {:status :ready}
      (do
        (println (str "Missing: " (str/join ", " (:missing validation))))
        (safe-shell "flox activate")
        {:status :activated}))))

;; ═══════════════════════════════════════════════════════════════
;; CLI
;; ═══════════════════════════════════════════════════════════════

(defn -main [& args]
  (cond
    (empty? args)
    (do
      (println "shell-guard: ENOENT prevention")
      (println "Usage: bb shell_guard.bb exec <cmd>")
      (println "       bb shell_guard.bb validate <cmd1> ...")
      (println "       bb shell_guard.bb info")
      (println)
      (prn (shell-info)))
    
    (= (first args) "exec")
    (let [cmd (str/join " " (rest args))
          result (safe-shell cmd)]
      (print (:out result))
      (System/exit (:exit result 0)))
    
    (= (first args) "validate")
    (let [result (validate-env (rest args))]
      (if (:valid result)
        (println "✓ All available")
        (do (println (str "✗ Missing: " (str/join ", " (:missing result))))
            (System/exit 1))))
    
    (= (first args) "info")
    (prn (shell-info))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
