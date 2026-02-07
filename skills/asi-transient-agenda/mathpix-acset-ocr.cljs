#!/usr/bin/env bb
;; mathpix-acset-ocr.cljs — Mathpix OCR → Universal ACSet Format
;; Bridges image/PDF OCR to ACSet-compatible JSON for AlgebraicJulia
;;
;; Usage:
;;   bb mathpix-acset-ocr.cljs image diagram.png
;;   bb mathpix-acset-ocr.cljs url https://example.com/diagram.jpg
;;   bb mathpix-acset-ocr.cljs pdf paper.pdf
;;   bb mathpix-acset-ocr.cljs parse-latex '\xymatrix{A \ar[r]^f & B}'

(require '[babashka.http-client :as http]
         '[cheshire.core :as json]
         '[clojure.string :as str]
         '[clojure.java.io :as io])

(import '[java.util Base64])

;; ═══════════════════════════════════════════════
;; Mathpix API client
;; ═══════════════════════════════════════════════

(def app-id (or (System/getenv "MATHPIX_APP_ID")
                "barton_plurigrid_xyz_603481_aace6b"))
(def app-key (System/getenv "MATHPIX_APP_KEY"))

(def api-base "https://api.mathpix.com/v3")

(defn auth-headers []
  {"app_id"       app-id
   "app_key"      app-key
   "Content-Type" "application/json"})

(defn image->base64 [path]
  (let [bytes (.readAllBytes (io/input-stream path))
        ext   (last (str/split path #"\."))]
    (str "data:image/" (case ext "jpg" "jpeg" "jpeg" "jpeg" ext)
         ";base64,"
         (.encodeToString (Base64/getEncoder) bytes))))

(defn ocr-image [path]
  (let [body (json/generate-string
               {:src     (image->base64 path)
                :formats ["text" "latex_styled" "mathml"]
                :include_line_data true})
        resp (http/post (str api-base "/text")
               {:headers (auth-headers)
                :body    body})]
    (json/parse-string (:body resp) true)))

(defn ocr-url [url]
  (let [body (json/generate-string
               {:src     url
                :formats ["text" "latex_styled" "mathml"]
                :include_line_data true})
        resp (http/post (str api-base "/text")
               {:headers (auth-headers)
                :body    body})]
    (json/parse-string (:body resp) true)))

(defn ocr-pdf [path]
  (let [bytes  (.readAllBytes (io/input-stream path))
        b64    (.encodeToString (Base64/getEncoder) bytes)
        body   (json/generate-string
                 {:src (str "data:application/pdf;base64," b64)
                  :conversion_formats {:md true :tex.zip true}})
        resp   (http/post (str api-base "/pdf")
                 {:headers (auth-headers)
                  :body    body})
        result (json/parse-string (:body resp) true)]
    ;; PDF is async — return the pdf_id for polling
    result))

;; ═══════════════════════════════════════════════
;; LaTeX → ACSet diagram parser
;; ═══════════════════════════════════════════════

(defn extract-tikzcd-nodes
  "Extract nodes from tikz-cd LaTeX."
  [latex]
  (let [;; Find node labels (single uppercase or \mathcal{X} patterns)
        node-re   #"(?:(?:\\mathcal\{([^}]+)\})|([A-Z][a-z0-9']*)|(\d+)|([0])|(?:\\text\{([^}]+)\}))"
        ;; Find arrows with labels
        arrow-re  #"\\arrow\[([^\]]+?)(?:,\s*\"([^\"]*?)\")?(?:'?)?\]"
        ;; Direction shorthands
        dir-map   {"r" [0 1] "l" [0 -1] "d" [1 0] "u" [-1 0]
                    "dr" [1 1] "dl" [1 -1] "ur" [-1 1] "ul" [-1 -1]
                    "rr" [0 2] "dd" [2 0] "ll" [0 -2] "uu" [-2 0]}
        ;; Split into rows on \\ (two literal backslashes)
        rows      (str/split latex #"\\\\")
        nodes     (atom [])
        arrows    (atom [])]
    ;; Parse grid positions
    (doseq [[row-idx row-str] (map-indexed vector rows)]
      (let [cells (str/split (str/trim row-str) #"&")]
        (doseq [[col-idx cell] (map-indexed vector cells)]
          (let [cell-trimmed (str/trim cell)]
            ;; Extract node name
            (when-let [m (re-find #"(?:\\mathcal\{([^}]+)\}|([A-Z][a-z0-9']*)|(\d))" cell-trimmed)]
              (let [label (or (nth m 1) (nth m 2) (nth m 3))]
                (when label
                  (swap! nodes conj {:id    (count @nodes)
                                     :label label
                                     :row   row-idx
                                     :col   col-idx}))))
            ;; Extract arrows from this cell
            (doseq [[_ opts lbl] (re-seq arrow-re cell-trimmed)]
              (let [parts    (str/split opts #",\s*")
                    dir-str  (first (filter #(contains? dir-map (str/trim %)) parts))
                    dir      (when dir-str (get dir-map (str/trim dir-str)))
                    arrow-label (or lbl
                                   (some->> parts
                                            (filter #(re-find #"^\"" (str/trim %)))
                                            first
                                            (re-find #"\"([^\"]+)\"")
                                            second))]
                (when dir
                  (swap! arrows conj
                         {:src-pos  [row-idx col-idx]
                          :tgt-pos  [(+ row-idx (first dir))
                                     (+ col-idx (second dir))]
                          :label    (or arrow-label "")
                          :options  opts}))))))))
    {:nodes @nodes :arrows @arrows}))

(defn extract-xypic-nodes
  "Extract nodes from xy-pic \\xymatrix LaTeX."
  [latex]
  (let [;; Strip \xymatrix{...} wrapper and options like @R=3pc@C=4pc
        body    (or (second (re-find #"(?s)\\xymatrix(?:@[^{]*)*\{(.*)\}" latex))
                    latex)
        rows    (str/split body #"\\\\")
        nodes   (atom [])
        arrows  (atom [])]
    (doseq [[row-idx row-str] (map-indexed vector rows)]
      (let [cells (str/split (str/trim row-str) #"&")]
        (doseq [[col-idx cell] (map-indexed vector cells)]
          (let [cell-trimmed (str/trim cell)
                ;; Node label — match at start, skip leading \ar or \arrow
                label-m (re-find #"(?:^|(?<=&)\s*)(?:\\mathcal\{([^}]+)\}|([A-Z][a-z0-9']*)|(\d))" cell-trimmed)
                label   (when label-m (or (nth label-m 1) (nth label-m 2) (nth label-m 3)))]
            (when label
              (swap! nodes conj {:id    (count @nodes)
                                 :label label
                                 :row   row-idx
                                 :col   col-idx}))
            ;; xy-pic arrows: \ar[direction]^{label} or \ar@{type}[direction]
            (doseq [[_ _ dir lbl1 lbl2]
                    (re-seq #"\\ar(?:@\{([^}]*)\})?\[([a-z]+)\](?:\^?\{([^}]*)\}|_?\{([^}]*)\})?" cell-trimmed)]
              (let [dir-offsets (reduce (fn [acc c]
                                         (case (str c)
                                           "r" (update acc 1 inc)
                                           "l" (update acc 1 dec)
                                           "u" (update acc 0 dec)
                                           "d" (update acc 0 inc)
                                           acc))
                                       [0 0] dir)]
                (swap! arrows conj
                       {:src-pos  [row-idx col-idx]
                        :tgt-pos  [(+ row-idx (first dir-offsets))
                                   (+ col-idx (second dir-offsets))]
                        :label    (or lbl1 lbl2 "")
                        :options  dir})))))))
    {:nodes @nodes :arrows @arrows}))

(defn resolve-arrows
  "Resolve position-based arrows to node-id-based."
  [{:keys [nodes arrows]}]
  (let [pos->id (into {} (map (fn [n] [[(:row n) (:col n)] (:id n)]) nodes))]
    (keep (fn [a]
            (let [src-id (get pos->id (:src-pos a))
                  tgt-id (get pos->id (:tgt-pos a))]
              (when (and src-id tgt-id)
                {:src   src-id
                 :tgt   tgt-id
                 :label (:label a)})))
          arrows)))

;; ═══════════════════════════════════════════════
;; Universal ACSet JSON format
;; Congruent with ACSets.jl JSON serialization
;; ═══════════════════════════════════════════════

(defn diagram->acset
  "Convert parsed diagram to ACSet JSON (ACSets.jl compatible).
   Schema: FreeDiagram with Ob, Hom, AttrType=String, Attr=label"
  [parsed-diagram & {:keys [source-format confidence source-url]
                     :or   {source-format "unknown" confidence 0.0}}]
  (let [nodes          (:nodes parsed-diagram)
        resolved       (resolve-arrows parsed-diagram)
        ;; ACSet schema (FreeDiagram)
        schema         {:version    {:ACSetSchema "0.0.1"
                                     :ACSets      "0.2.0"
                                     :asi-ocr     "1.0.0"}
                        :Ob         [{:name "Ob"} {:name "Hom"}]
                        :Hom        [{:name "src" :dom "Hom" :codom "Ob"}
                                     {:name "tgt" :dom "Hom" :codom "Ob"}]
                        :AttrType   [{:name "Label"} {:name "MathML"} {:name "LaTeX"}]
                        :Attr       [{:name "ob_label"  :dom "Ob"  :codom "Label"}
                                     {:name "hom_label" :dom "Hom" :codom "Label"}]
                        :equations  []}
        ;; ACSet instance data
        instance       {:Ob   (mapv (fn [n]
                                      {:_id      (inc (:id n))
                                       :ob_label (:label n)})
                                    nodes)
                        :Hom  (mapv (fn [a i]
                                     {:_id       (inc i)
                                      :src       (inc (:src a))
                                      :tgt       (inc (:tgt a))
                                      :hom_label (:label a)})
                                   resolved (range))}
        ;; Provenance metadata (not part of ACSet spec but useful)
        provenance     {:ocr_engine     (when confidence "mathpix")
                        :confidence     confidence
                        :source_format  source-format
                        :source_url     source-url
                        :extraction_ts  (.toString (java.time.Instant/now))
                        :seed           1069}]
    {:schema     schema
     :instance   instance
     :provenance provenance}))

(defn latex->acset
  "Parse LaTeX diagram string to ACSet JSON."
  [latex]
  (let [is-tikzcd (str/includes? latex "tikzcd")
        is-xypic  (or (str/includes? latex "xymatrix")
                      (str/includes? latex "\\ar["))
        parsed    (cond
                    is-tikzcd (extract-tikzcd-nodes latex)
                    is-xypic  (extract-xypic-nodes latex)
                    :else     {:nodes [] :arrows []})]
    (diagram->acset parsed
                    :source-format (cond is-tikzcd "tikz-cd"
                                         is-xypic  "xy-pic"
                                         :else     "unknown"))))

(defn mathpix->acset
  "Full pipeline: image/URL → Mathpix OCR → ACSet."
  [ocr-result source-url]
  (let [latex      (or (:latex_styled ocr-result) (:text ocr-result) "")
        confidence (or (:confidence ocr-result) 0.0)
        ;; Try to parse any tikz-cd or xy-pic in the output
        acset      (latex->acset latex)]
    (-> acset
        (assoc-in [:provenance :confidence] confidence)
        (assoc-in [:provenance :source_url] source-url)
        (assoc-in [:provenance :raw_latex] latex)
        (assoc-in [:provenance :raw_text] (:text ocr-result))
        (assoc-in [:provenance :mathml] (:mathml ocr-result)))))

;; ═══════════════════════════════════════════════
;; OLMoOCR / Mistral OCR compatibility layer
;; ═══════════════════════════════════════════════

(defn markdown->acset-hints
  "Extract diagram hints from Markdown output (OLMoOCR/Mistral format).
   These OCR engines output Markdown with LaTeX math blocks."
  [markdown]
  (let [;; Find LaTeX math blocks
        display-math (re-seq #"\$\$(.*?)\$\$" markdown)
        inline-math  (re-seq #"(?<!\$)\$([^\$]+?)\$(?!\$)" markdown)
        ;; Find tikz-cd or xy-pic environments
        tikzcd-envs  (re-seq #"(?s)\\begin\{tikzcd\}(.*?)\\end\{tikzcd\}" markdown)
        xypic-envs   (re-seq #"(?s)\\xymatrix\{(.*?)\}" markdown)
        ;; Parse each environment into ACSets
        acsets       (concat
                       (map (fn [[full body]]
                              (latex->acset (str "\\begin{tikzcd}" body "\\end{tikzcd}")))
                            tikzcd-envs)
                       (map (fn [[full body]]
                              (latex->acset (str "\\xymatrix{" body "}")))
                            xypic-envs))]
    {:diagrams        (vec acsets)
     :math_blocks     (mapv second display-math)
     :inline_math     (mapv second inline-math)
     :source_format   "markdown-ocr"
     :diagram_count   (count acsets)}))

;; ═══════════════════════════════════════════════
;; CLI dispatch
;; ═══════════════════════════════════════════════

(defn -main [& args]
  (when (or (empty? args) (= (first args) "--help"))
    (println "Usage:")
    (println "  bb mathpix-acset-ocr.cljs image <path>       OCR image → ACSet JSON")
    (println "  bb mathpix-acset-ocr.cljs url <url>          OCR URL → ACSet JSON")
    (println "  bb mathpix-acset-ocr.cljs pdf <path>         OCR PDF (async) → pdf_id")
    (println "  bb mathpix-acset-ocr.cljs parse-latex <tex>  Parse LaTeX → ACSet JSON")
    (println "  bb mathpix-acset-ocr.cljs parse-md <path>    Parse Markdown → ACSet JSON")
    (System/exit 0))

  (let [cmd  (first args)
        arg  (second args)]
    (case cmd
      "image"
      (let [result (ocr-image arg)
            acset  (mathpix->acset result arg)]
        (println (json/generate-string acset {:pretty true})))

      "url"
      (let [result (ocr-url arg)
            acset  (mathpix->acset result arg)]
        (println (json/generate-string acset {:pretty true})))

      "pdf"
      (let [result (ocr-pdf arg)]
        (println (json/generate-string result {:pretty true})))

      "parse-latex"
      (let [acset (latex->acset arg)]
        (println (json/generate-string acset {:pretty true})))

      "parse-md"
      (let [md     (slurp arg)
            result (markdown->acset-hints md)]
        (println (json/generate-string result {:pretty true})))

      (do (println "Unknown command:" cmd)
          (System/exit 1)))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
