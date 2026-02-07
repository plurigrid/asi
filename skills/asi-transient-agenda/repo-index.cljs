(ns asi-transient-agenda.repo-index
  (:require ["child_process" :as cp]
            ["fs" :as fs]))

(defn gh-repos []
  (-> (cp/execSync
       "gh repo list plurigrid --limit 400 --json name,description,primaryLanguage,updatedAt,isArchived,stargazerCount"
       #js {:encoding "utf-8" :maxBuffer (* 10 1024 1024)})
      js/JSON.parse
      (js->clj :keywordize-keys true)))

(defn by-language [repos]
  (->> repos
       (remove :isArchived)
       (group-by #(get-in % [:primaryLanguage :name] "none"))))

(defn format-repo [{:keys [name description stargazerCount]}]
  (str "  " name
       (when (pos? stargazerCount) (str " [" stargazerCount "*]"))
       (when description (str " — " (subs description 0 (min 60 (count description)))))))

(defn render-agenda [repos]
  (let [grouped (by-language repos)
        sorted  (sort-by (comp - count val) grouped)]
    (doseq [[lang items] sorted]
      (println (str "** " lang " (" (count items) " repos)"))
      (doseq [r (sort-by :name items)]
        (println (format-repo r)))
      (println))))

(defn emit-elisp-data [repos]
  (let [grouped (by-language repos)]
    (str "'("
         (apply str
                (interpose
                 " "
                 (map (fn [[k v]]
                        (str "(\"" k "\" . ("
                             (apply str
                                    (interpose
                                     " "
                                     (map #(str "\"" (:name %) "\"") v)))
                             "))"))
                      grouped)))
         ")")))

(defn -main []
  (let [repos (gh-repos)
        elisp (emit-elisp-data repos)]
    (render-agenda repos)
    (fs/writeFileSync "/tmp/asi-repos.el" elisp "utf-8")
    (println (str "--- " (count repos) " repos indexed, elisp written to /tmp/asi-repos.el"))))

(-main)
