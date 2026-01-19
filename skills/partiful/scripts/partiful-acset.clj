#!/usr/bin/env bb

;; Partiful ACSet Schema - Category-theoretic event modeling
;; Maps Partiful data to attributed C-sets

(ns partiful-acset
  (:require [cheshire.core :as json]
            [clojure.string :as str]))

;; ============================================================
;; ACSet Schema Definition (Catlab-style)
;; ============================================================

;; Schema: Partiful as a category
;; 
;;   Event ←──host──── User
;;     ↑                 ↑
;;     │                 │
;;  event_of          invitee
;;     │                 │
;;     └─── Invite ─────┘
;;            ↓
;;          RSVP
;;
;; Attributes:
;;   Event: {name, date, location, description, url}
;;   User: {name, username, avatar}
;;   Invite: {sent_at, source}
;;   RSVP: {status ∈ {GOING, MAYBE, DECLINED, PENDING}, responded_at}

(def schema
  {:objects #{:Event :User :Invite :RSVP}
   :morphisms {:host [:Event :User]
               :invitee [:Invite :User]
               :event_of [:Invite :Event]
               :rsvp_invite [:RSVP :Invite]}
   :attributes {:Event {:name :String
                        :date :DateTime
                        :location :String
                        :description :String
                        :url :String
                        :capacity :Int}
                :User {:name :String
                       :username :String
                       :avatar :String
                       :user_id :String}
                :Invite {:sent_at :DateTime
                         :source :String}
                :RSVP {:status :RSVPStatus
                       :responded_at :DateTime}}})

;; ============================================================
;; ACSet Instance (In-memory C-set)
;; ============================================================

(defn make-acset
  "Create empty ACSet instance for Partiful schema"
  []
  {:parts {:Event []
           :User []
           :Invite []
           :RSVP []}
   :morphisms {:host {}      ;; Event-id → User-id
               :invitee {}   ;; Invite-id → User-id
               :event_of {}  ;; Invite-id → Event-id
               :rsvp_invite {}} ;; RSVP-id → Invite-id
   :indices {:Event-by-id {}
             :User-by-id {}
             :User-by-username {}}})

(defn add-part!
  "Add a part to an object, return its index"
  [acset obj data]
  (let [idx (count (get-in @acset [:parts obj]))]
    (swap! acset update-in [:parts obj] conj (assoc data :_idx idx))
    ;; Update indices
    (when-let [id (:id data)]
      (swap! acset assoc-in [:indices (keyword (str (name obj) "-by-id")) id] idx))
    (when (and (= obj :User) (:username data))
      (swap! acset assoc-in [:indices :User-by-username (:username data)] idx))
    idx))

(defn set-morphism!
  "Set morphism value: src-idx maps to tgt-idx"
  [acset morph src-idx tgt-idx]
  (swap! acset assoc-in [:morphisms morph src-idx] tgt-idx))

(defn get-part
  "Get part by object type and index"
  [acset obj idx]
  (get-in @acset [:parts obj idx]))

(defn get-parts
  "Get all parts of an object type"
  [acset obj]
  (get-in @acset [:parts obj]))

(defn lookup-by-id
  "Find part index by external ID"
  [acset obj id]
  (get-in @acset [:indices (keyword (str (name obj) "-by-id")) id]))

(defn incident
  "Get all source indices that map to target via morphism"
  [acset morph tgt-idx]
  (let [m (get-in @acset [:morphisms morph])]
    (keep (fn [[src tgt]] (when (= tgt tgt-idx) src)) m)))

;; ============================================================
;; Partiful → ACSet Transformation
;; ============================================================

(defn import-user!
  "Import user data, return index (or existing if duplicate)"
  [acset user-data]
  (let [user-id (:id user-data (:userId user-data))]
    (if-let [existing (lookup-by-id acset :User user-id)]
      existing
      (add-part! acset :User
                 {:id user-id
                  :name (:name user-data (:displayName user-data))
                  :username (:username user-data)
                  :avatar (:avatarUrl user-data (:avatar user-data))}))))

(defn import-event!
  "Import event data, return index"
  [acset event-data]
  (let [event-id (:id event-data)]
    (if-let [existing (lookup-by-id acset :Event event-id)]
      existing
      (let [event-idx (add-part! acset :Event
                                  {:id event-id
                                   :name (:name event-data (:title event-data))
                                   :date (:startDate event-data (:date event-data))
                                   :location (:location event-data)
                                   :description (:description event-data)
                                   :url (str "https://partiful.com/e/" event-id)
                                   :capacity (:maxCapacity event-data)})]
        ;; Set host morphism if host data present
        (when-let [host (:host event-data (:creator event-data))]
          (let [host-idx (import-user! acset host)]
            (set-morphism! acset :host event-idx host-idx)))
        event-idx))))

(defn import-invite!
  "Import invite relationship"
  [acset {:keys [event user status sent-at source]}]
  (let [event-idx (if (map? event) 
                    (import-event! acset event)
                    (lookup-by-id acset :Event event))
        user-idx (if (map? user)
                   (import-user! acset user)
                   (lookup-by-id acset :User user))
        invite-idx (add-part! acset :Invite
                              {:sent_at sent-at
                               :source source})]
    ;; Set morphisms
    (when event-idx (set-morphism! acset :event_of invite-idx event-idx))
    (when user-idx (set-morphism! acset :invitee invite-idx user-idx))
    ;; Add RSVP if status present
    (when status
      (let [rsvp-idx (add-part! acset :RSVP {:status status})]
        (set-morphism! acset :rsvp_invite rsvp-idx invite-idx)))
    invite-idx))

;; ============================================================
;; Query Combinators (Specter-style)
;; ============================================================

(defn select-where
  "Select parts matching predicate"
  [acset obj pred]
  (filter pred (get-parts acset obj)))

(defn navigate
  "Navigate morphism from source"
  [acset morph src-idx]
  (get-in @acset [:morphisms morph src-idx]))

(defn navigate-inverse
  "Navigate inverse of morphism (all sources mapping to target)"
  [acset morph tgt-idx]
  (incident acset morph tgt-idx))

;; Query: "All events I'm invited to"
(defn my-invited-events
  [acset my-user-idx]
  (let [my-invites (navigate-inverse acset :invitee my-user-idx)
        event-idxs (map #(navigate acset :event_of %) my-invites)]
    (map #(get-part acset :Event %) (filter some? event-idxs))))

;; Query: "All guests for an event"
(defn event-guests
  [acset event-idx]
  (let [invites (navigate-inverse acset :event_of event-idx)
        user-idxs (map #(navigate acset :invitee %) invites)]
    (map #(get-part acset :User %) (filter some? user-idxs))))

;; Query: "RSVP status for event"
(defn event-rsvps
  [acset event-idx]
  (let [invites (navigate-inverse acset :event_of event-idx)]
    (for [inv-idx invites
          :let [rsvp-idxs (navigate-inverse acset :rsvp_invite inv-idx)
                user-idx (navigate acset :invitee inv-idx)
                user (get-part acset :User user-idx)]
          rsvp-idx rsvp-idxs
          :let [rsvp (get-part acset :RSVP rsvp-idx)]]
      {:user user :status (:status rsvp)})))

;; ============================================================
;; GF(3) Color Integration
;; ============================================================

(defn gay-color
  "Generate deterministic color from seed and index"
  [seed idx]
  (let [golden (unchecked-multiply (bit-xor seed idx) 0x9E3779B97F4A7C15)
        h (mod (bit-shift-right golden 16) 360)
        trit (cond (or (< h 60) (>= h 300)) 1
                   (< h 180) 0
                   :else -1)]
    {:hue h
     :trit trit
     :hex (format "#%02X%02X%02X"
                  (int (* 255 (+ 0.5 (* 0.5 (Math/cos (Math/toRadians h))))))
                  (int (* 255 (+ 0.5 (* 0.5 (Math/cos (Math/toRadians (- h 120)))))))
                  (int (* 255 (+ 0.5 (* 0.5 (Math/cos (Math/toRadians (- h 240))))))))
     }))

(defn color-acset-parts
  "Assign GF(3) colors to all parts"
  [acset seed]
  (let [all-parts (mapcat (fn [[obj parts]]
                            (map-indexed (fn [i p] 
                                          {:obj obj :idx i :part p}) 
                                        parts))
                          (get-in @acset [:parts]))]
    (map-indexed (fn [i {:keys [obj idx part]}]
                   (assoc part 
                          :_color (gay-color seed i)
                          :_obj obj
                          :_idx idx))
                 all-parts)))

;; ============================================================
;; Export / Serialize
;; ============================================================

(defn acset->json
  "Export ACSet to JSON"
  [acset]
  (json/generate-string @acset {:pretty true}))

(defn acset->edn
  "Export ACSet to EDN"
  [acset]
  (pr-str @acset))

;; ============================================================
;; Demo
;; ============================================================

(defn demo []
  (let [acset (atom (make-acset))]
    ;; Import sample data
    (import-event! acset {:id "abc123"
                          :name "Music Show at Avalon"
                          :date "2026-01-25T19:00:00"
                          :location "Avalon"
                          :host {:id "user1" :name "Jonathan Wallis"}})
    
    (import-invite! acset {:event "abc123"
                           :user {:id "user2" :name "Alice"}
                           :status "GOING"})
    
    (import-invite! acset {:event "abc123"
                           :user {:id "user3" :name "Bob"}
                           :status "MAYBE"})
    
    ;; Query
    (println "Event guests:")
    (doseq [guest (event-guests acset 0)]
      (println "  -" (:name guest)))
    
    (println "\nRSVPs:")
    (doseq [{:keys [user status]} (event-rsvps acset 0)]
      (println "  -" (:name user) "->" status))
    
    (println "\nColored parts (seed=1069):")
    (doseq [p (color-acset-parts acset 1069)]
      (println "  " (:_obj p) (:_idx p) 
               (:name p (:status p)) 
               "→" (get-in p [:_color :hex])
               "trit:" (get-in p [:_color :trit])))
    
    acset))

(when (= *file* (System/getProperty "babashka.file"))
  (demo))
