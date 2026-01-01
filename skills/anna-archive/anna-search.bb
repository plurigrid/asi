#!/usr/bin/env bb
;; anna-search.bb - Search Anna's Archive for books and papers

(require '[babashka.http-client :as http]
         '[clojure.string :as str]
         '[babashka.cli :as cli])

(def base-url "https://annas-archive.org")

(defn build-search-url [query opts]
  (let [params (cond-> {"q" query}
                 (:lang opts) (assoc "lang" (:lang opts))
                 (:ext opts) (assoc "ext" (:ext opts))
                 (:content opts) (assoc "content" (:content opts)))]
    (str base-url "/search?" 
         (str/join "&" (map #(str (first %) "=" (second %)) params)))))

(defn search [query opts]
  (let [url (build-search-url query opts)]
    (println (format "🔍 Searching Anna's Archive: %s" query))
    (println (format "   URL: %s" url))
    {:query query
     :url url
     :params opts
     :note "Open URL in browser or use scraper for results"}))

(defn fetch-md5 [md5]
  (let [url (format "%s/md5/%s" base-url md5)]
    (println (format "📖 Fetching document: %s" md5))
    (println (format "   URL: %s" url))
    {:md5 md5 :url url}))

(defn triadic-search [queries]
  (println "\n🔺 TRIADIC SEARCH (GF(3) Balanced)")
  (println "════════════════════════════════════════════════")
  (let [trits (cycle [-1 0 1])
        results (map-indexed 
                  (fn [i q]
                    (let [trit (nth (cycle [-1 0 1]) i)]
                      (println (format "  [%+d] %s" trit q))
                      {:query q :trit trit :url (build-search-url q {})}))
                  (take 3 queries))
        sum (reduce + (map :trit results))]
    (println)
    (println (format "  GF(3) Sum: %d (mod 3 = %d) %s" 
                     sum (mod sum 3) 
                     (if (zero? (mod sum 3)) "✓ BALANCED" "⚠ UNBALANCED")))
    {:results results :gf3-sum sum :balanced? (zero? (mod sum 3))}))

(def cli-spec
  {:query {:coerce :string :desc "Search query"}
   :lang {:coerce :string :default "en" :desc "Language filter"}
   :ext {:coerce :string :default "pdf" :desc "File extension"}
   :content {:coerce :string :default "book_nonfiction" :desc "Content type"}
   :md5 {:coerce :string :desc "Fetch by MD5 hash"}
   :triadic {:coerce :boolean :desc "Triadic search (3 queries)"}})

(defn -main [& args]
  (let [opts (cli/parse-opts args {:spec cli-spec})
        queries (if (seq (:args opts)) 
                  (vec (:args opts))
                  (filterv #(not (str/starts-with? % "-")) args))]
    (cond
      (:md5 opts)
      (fetch-md5 (:md5 opts))
      
      (:triadic opts)
      (if (>= (count queries) 3)
        (triadic-search queries)
        (println "Error: --triadic requires 3 queries"))
      
      (seq queries)
      (search (first queries) opts)
      
      :else
      (do
        (println "Anna's Archive Search")
        (println "═══════════════════════════════════════════════")
        (println "Usage:")
        (println "  bb anna-search.bb \"category theory\"")
        (println "  bb anna-search.bb \"homotopy\" --lang en --ext pdf")
        (println "  bb anna-search.bb --md5 abc123def456")
        (println "  bb anna-search.bb --triadic \"query1\" \"query2\" \"query3\"")
        (println)
        (println "Content types: book_nonfiction, book_fiction, journal_article")
        (println "Extensions: pdf, epub, djvu, mobi")))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
