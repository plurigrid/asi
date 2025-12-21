(ns music-topos.biff-app
  "Biff + HTMX + Gay.jl Color Palette Narrative Application

   Two-choice narrative branching with maximum interaction entropy:
   - Fork Reality: Branch into alternate timeline
   - Continue: Progress in current timeline

   Color palette guides semantic flow via golden angle rotation.
   Hosted maximally on Clojure with Therm (thermal dynamics) and Hyjax.
   "
  (:require [biff.core :as biff]
            [biff.crux :as crux]
            [biff.htmx :as htmx]
            [ring.util.response :as ring-resp]
            [hiccup.core :as hiccup]
            [clojure.edn :as edn]
            [clj-http.client :as http]))

;; ============================================================================
;; GOLDEN ANGLE COLOR PALETTE (Gay.jl)
;; ============================================================================

(def ^:const GOLDEN_ANGLE 137.508)  ; φ² golden angle
(def ^:const PHI 1.618034)           ; golden ratio

(defn compute-hue
  "Compute hue based on index using golden angle rotation"
  [index]
  (mod (* index GOLDEN_ANGLE) 360))

(defn compute-saturation
  "Saturation increases with interaction depth (entropy)"
  [depth complexity]
  (let [base-sat (+ 0.3 (/ depth 20))
        entropy-factor (/ complexity 10)]
    (min 1.0 (+ base-sat entropy-factor))))

(defn compute-lightness
  "Lightness represents narrative tension/certainty"
  [certainty depth]
  (let [base (+ 0.3 certainty)
        depth-factor (/ depth 10)]
    (min 0.9 (max 0.2 (- base depth-factor)))))

(defn hsl-to-rgb
  "Convert HSL to RGB"
  [hue saturation lightness]
  (let [c (* saturation (- 1 (Math/abs (- (* 2 lightness) 1))))
        x (* c (- 1 (Math/abs (mod (/ hue 60) 2))))
        m (- lightness (/ c 2))
        [r' g' b'] (cond
                     (<= hue 60)   [c x 0]
                     (<= hue 120)  [x c 0]
                     (<= hue 180)  [0 c x]
                     (<= hue 240)  [0 x c]
                     (<= hue 300)  [x 0 c]
                     :else         [c 0 x])
        [r g b] [(+ r' m) (+ g' m) (+ b' m)]]
    [(int (* r 255)) (int (* g 255)) (int (* b 255))]))

(defn color-at
  "Get color at specific narrative state index"
  [idx depth certainty complexity]
  (let [hue (compute-hue idx)
        sat (compute-saturation depth complexity)
        light (compute-lightness certainty depth)
        [r g b] (hsl-to-rgb hue sat light)
        hex (format "#%02x%02x%02x" r g b)]
    {:index idx
     :hue hue
     :saturation sat
     :lightness light
     :rgb [r g b]
     :hex hex
     :depth depth
     :certainty certainty}))

;; ============================================================================
;; NARRATIVE STATE MACHINE
;; ============================================================================

(defprotocol INarrativeState
  "Protocol for narrative branching states"
  (current-color [this])
  (next-states [this])
  (fork-branch [this name description])
  (continue-branch [this]))

(defrecord NarrativeNode
  [id depth timeline text choices color history entropy]
  INarrativeState
  (current-color [_] color)
  (next-states [_] choices)
  (fork-branch [this name desc]
    (let [new-id (str id ":fork:" name)
          new-depth (inc depth)
          new-timeline (conj timeline :fork)
          new-entropy (inc entropy)
          new-color (color-at new-id new-depth 0.3 new-entropy)]
      (->NarrativeNode new-id new-depth new-timeline desc [] new-color
                       (conj history id) new-entropy)))
  (continue-branch [this]
    (let [new-id (str id ":cont")
          new-depth (inc depth)
          new-timeline (conj timeline :continue)
          new-entropy (+ entropy 0.1)
          new-color (color-at new-id new-depth 0.7 new-entropy)]
      (->NarrativeNode new-id new-depth new-timeline
                       (str "Continuing from: " text) [] new-color
                       (conj history id) new-entropy))))

(defn initial-narrative-state
  "Create the initial narrative node"
  []
  (let [color (color-at 0 0 1.0 1)]
    (->NarrativeNode
      "root"
      0
      []
      "Welcome to the Narrative Fork Engine. Two paths diverge..."
      [{:label "Fork Reality" :action :fork}
       {:label "Continue" :action :continue}]
      color
      []
      0)))

;; ============================================================================
;; THERM - THERMAL DYNAMICS FOR INTERACTION HEAT
;; ============================================================================

(defn compute-thermal-intensity
  "Heat increases with interaction frequency and complexity"
  [action-count complexity depth]
  (let [frequency-heat (min 1.0 (/ action-count 10))
        complexity-heat (/ complexity 10)
        depth-heat (/ depth 20)]
    (+ frequency-heat complexity-heat depth-heat)))

(defn thermal-color-adjustment
  "Adjust color based on thermal intensity (heat)"
  [base-color thermal-intensity]
  (let [{:keys [lightness saturation]} base-color
        adjusted-light (+ lightness (* thermal-intensity 0.2))
        adjusted-sat (+ saturation (* thermal-intensity 0.1))]
    (assoc base-color
      :lightness (min 0.9 adjusted-light)
      :saturation (min 1.0 adjusted-sat))))

;; ============================================================================
;; HYJAX - HYBRID INTERACTION ENGINE (Hy + AJAX)
;; ============================================================================

(defn htmx-action
  "Create an HTMX action for narrative branching"
  [action-type target-node]
  {:hx-post (str "/narrative/" action-type)
   :hx-target "#narrative-container"
   :hx-swap "innerHTML"
   :data-node target-node})

(defn render-narrative-choice
  "Render a single choice button with color and HTMX binding"
  [choice-idx color {:keys [label action]}]
  [:button.narrative-choice
   {:style (str "background-color: " (:hex color)
                "; color: white; border: none; padding: 10px 20px; "
                "margin: 5px; cursor: pointer; border-radius: 5px;")
    :hx-post (str "/narrative/" action)
    :hx-target "#narrative-container"
    :hx-swap "innerHTML"
    :data-action action}
   label])

(defn render-narrative-state
  "Render the current narrative state with interactive choices"
  [state action-count]
  (let [{:keys [id text choices color depth entropy]} state
        thermal (compute-thermal-intensity action-count (count choices) depth)
        adjusted-color (thermal-color-adjustment color thermal)]
    [:div#narrative-container
     {:style (str "background: linear-gradient(135deg, " (:hex adjusted-color)
                  " 0%, #000000 100%); padding: 30px; border-radius: 10px; "
                  "color: white; font-family: monospace; min-height: 300px;")}
     [:h1 {:style "color: white;"} text]
     [:p {:style "font-size: 12px; opacity: 0.7;"}
      (str "Path: " (clojure.string/join " → " (:timeline state)) " | "
           "Depth: " depth " | "
           "Entropy: " (format "%.2f" entropy) " | "
           "Thermal: " (format "%.2f" thermal))]
     [:div#choices
      (map-indexed
        (fn [idx choice]
          (let [choice-color (color-at (+ idx (* depth 10))
                                        (inc depth)
                                        (- 1.0 thermal)
                                        (count choices))]
            (render-narrative-choice idx choice-color choice)))
        choices)]
     [:style {:dangerously-set-inner-html
              (str ".narrative-choice:hover { opacity: 0.8; transition: opacity 0.3s; }")}]]))

;; ============================================================================
;; BIFF HANDLERS
;; ============================================================================

(defn narrative-handler
  "Main narrative state handler"
  [req]
  (let [state (or (get-in req [:session :narrative-state])
                  (initial-narrative-state))
        action-count (or (get-in req [:session :action-count]) 0)]
    {:status 200
     :body (hiccup/html (render-narrative-state state action-count))}))

(defn fork-reality-handler
  "Handle fork reality action"
  [{:keys [params session] :as req}]
  (let [current-state (get session :narrative-state (initial-narrative-state))
        new-state (.fork-branch current-state "branch" "Forking into alternate reality")
        new-action-count (inc (or (get session :action-count) 0))]
    {:status 200
     :session (assoc session
                :narrative-state new-state
                :action-count new-action-count)
     :body (hiccup/html (render-narrative-state new-state new-action-count))}))

(defn continue-handler
  "Handle continue action"
  [{:keys [session] :as req}]
  (let [current-state (get session :narrative-state (initial-narrative-state))
        new-state (.continue-branch current-state)
        new-action-count (inc (or (get session :action-count) 0))]
    {:status 200
     :session (assoc session
                :narrative-state new-state
                :action-count new-action-count)
     :body (hiccup/html (render-narrative-state new-state new-action-count))}))

(defn reset-handler
  "Reset to initial state"
  [req]
  {:status 200
   :session (dissoc (:session req) :narrative-state :action-count)
   :body (hiccup/html (render-narrative-state (initial-narrative-state) 0))})

;; ============================================================================
;; BIFF APPLICATION SETUP
;; ============================================================================

(def routes
  [
   ["/narrative" :get narrative-handler]
   ["/narrative/fork" :post fork-reality-handler]
   ["/narrative/continue" :post continue-handler]
   ["/narrative/reset" :post reset-handler]])

(defn app
  []
  (biff/handler
    {:routes routes
     :session {:max-age (* 24 60 60)  ; 24 hours
               :cookie-attrs {:secure true :http-only true}}
     :middleware [[biff.crux/wrap-txs]
                  [biff.htmx/wrap-htmx]]}))

;; ============================================================================
;; MAIN PAGE WITH COLOR PALETTE GUIDE
;; ============================================================================

(defn root-handler
  [req]
  (let [initial-state (initial-narrative-state)]
    {:status 200
     :headers {"content-type" "text/html; charset=utf-8"}
     :body (hiccup/html
      [:html
       [:head
        [:title "Narrative Fork Engine - Color Guided Reality Branching"]
        [:meta {:charset "utf-8"}]
        [:meta {:name "viewport" :content "width=device-width, initial-scale=1"}]
        [:script {:src "https://unpkg.com/htmx.org"}]
        [:style
         "body { margin: 0; padding: 20px; background: #0a0a0a; color: #fff; font-family: 'Courier New', monospace; }"
         ".container { max-width: 900px; margin: 0 auto; }"
         ".title { font-size: 24px; font-weight: bold; margin-bottom: 20px; }"
         ".subtitle { opacity: 0.7; margin-bottom: 30px; }"
         ".color-palette { display: grid; grid-template-columns: repeat(12, 1fr); gap: 5px; margin: 30px 0; }"
         ".color-swatch { height: 40px; border-radius: 5px; cursor: pointer; }"
         ".info-section { background: #1a1a1a; padding: 15px; border-radius: 5px; margin: 15px 0; border-left: 3px solid #666; }"
         ".info-section h3 { margin-top: 0; }"]]
       [:body
        [:div.container
         [:div.title "🌈 NARRATIVE FORK ENGINE"]
         [:div.subtitle "Color-guided reality branching with maximum entropy interaction"]

         [:div.info-section
          [:h3 "🎨 Color Palette (Golden Angle: 137.508°)"]
          [:div.color-palette
           (for [i (range 12)]
             (let [c (color-at i 0 0.5 1)]
               [:div.color-swatch
                {:style (str "background-color: " (:hex c))
                 :title (str "Hue: " (format "%.1f" (:hue c)) "°")}]))]]

         [:div.info-section
          [:h3 "⚙️ How It Works"]
          [:p "1. Choose an action: Fork Reality or Continue"]
          [:p "2. Each action changes the color palette based on narrative depth"]
          [:p "3. Thermal intensity increases with interaction frequency"]
          [:p "4. Entropy guides the unpredictability of next states"]]

         [:div.info-section
          [:h3 "🔮 Begin Your Journey"]
          (render-narrative-state initial-state 0)]

         [:div.info-section
          [:button {:hx-post "/narrative/reset"
                   :hx-target "#narrative-container"
                   :hx-swap "innerHTML"
                   :style "background: #333; color: #fff; padding: 10px 20px; border: 1px solid #666; border-radius: 5px; cursor: pointer;"}
           "Reset Timeline"]]]]])}))

;; ============================================================================
;; RUNTIME
;; ============================================================================

(defn start!
  []
  (let [port 8080]
    (println (str "🚀 Narrative Fork Engine running on http://localhost:" port))
    (biff/start-system (app) {:port port})))

(defn -main
  [& args]
  (start!))
