#!/usr/bin/env bb

;; Partiful API Client - Babashka
;; Reverse-engineered unofficial API access

(ns partiful
  (:require [babashka.http-client :as http]
            [cheshire.core :as json]
            [clojure.string :as str]
            [babashka.fs :as fs]
            [babashka.process :refer [shell process]]))

;; ============================================================
;; Configuration
;; ============================================================

(def config-file (str (System/getProperty "user.home") "/.partiful-config.edn"))

(defn get-firebase-api-key []
  "Get Firebase API key from env or config. Must be obtained from Partiful web app."
  (or (System/getenv "PARTIFUL_FIREBASE_API_KEY")
      (throw (ex-info "PARTIFUL_FIREBASE_API_KEY not set. Extract from Partiful web app network requests." {}))))

(defn load-config []
  (if (fs/exists? config-file)
    (read-string (slurp config-file))
    {:auth-token (System/getenv "PARTIFUL_AUTH_TOKEN")
     :user-id (System/getenv "PARTIFUL_USER_ID")
     :refresh-token (System/getenv "PARTIFUL_REFRESH_TOKEN")}))

(defn save-config [config]
  (spit config-file (pr-str config))
  (println "Config saved to" config-file))

(defn decode-jwt-exp [token]
  "Extract expiration timestamp from JWT"
  (try
    (let [payload (second (str/split token #"\."))
          ;; Add padding for base64
          padded (str payload (apply str (repeat (mod (- 4 (mod (count payload) 4)) 4) "=")))
          decoded (String. (.decode (java.util.Base64/getUrlDecoder) padded))
          data (json/parse-string decoded true)]
      (:exp data))
    (catch Exception _ nil)))

(defn token-expired? [token]
  "Check if JWT token is expired (with 5 min buffer)"
  (if-let [exp (decode-jwt-exp token)]
    (< exp (+ (quot (System/currentTimeMillis) 1000) 300))
    true))

(defn refresh-firebase-token []
  "Use refresh token to get new access token from Firebase"
  (let [{:keys [refresh-token user-id]} (load-config)
        firebase-api-key (get-firebase-api-key)]
    (when refresh-token
      (println "Refreshing expired token...")
      (try
        (let [resp (http/request
                    {:method :post
                     :uri (str "https://securetoken.googleapis.com/v1/token?key=" firebase-api-key)
                     :headers {"Content-Type" "application/x-www-form-urlencoded"}
                     :body (str "grant_type=refresh_token&refresh_token=" refresh-token)})
              data (json/parse-string (:body resp) true)
              new-token (:id_token data)
              new-refresh (:refresh_token data)]
          (when new-token
            (save-config {:auth-token new-token
                          :refresh-token (or new-refresh refresh-token)
                          :user-id user-id})
            (println "Token refreshed successfully!")
            new-token))
        (catch Exception e
          (println "Failed to refresh token:" (.getMessage e))
          nil)))))

(defn get-valid-token []
  "Get a valid auth token, refreshing if needed"
  (let [{:keys [auth-token]} (load-config)]
    (if (and auth-token (not (token-expired? auth-token)))
      auth-token
      (or (refresh-firebase-token)
          (throw (ex-info "Token expired. Run: bb partiful.clj auth" {}))))))

;; ============================================================
;; API Client
;; ============================================================

(def base-url "https://api.partiful.com")

(defn api-request
  "Make authenticated request to Partiful API.
   Partiful uses POST requests with body: {:data {:params {} :userId user-id}}"
  [{:keys [method endpoint params body]}]
  (let [auth-token (get-valid-token)
        {:keys [user-id]} (load-config)
        resp (http/request
              {:method (or method :post)
               :uri (str base-url endpoint)
               :headers {"Authorization" (str "Bearer " auth-token)
                         "Content-Type" "application/json"
                         "Accept" "application/json"
                         "Origin" "https://partiful.com"
                         "Referer" "https://partiful.com/"}
               :body (json/generate-string
                      (or body {:data {:params (or params {})
                                       :userId user-id}}))})]
    (if (= 200 (:status resp))
      (json/parse-string (:body resp) true)
      (throw (ex-info "API error" {:status (:status resp)
                                    :body (:body resp)})))))

;; ============================================================
;; API Endpoints (discovered via reverse engineering)
;; ============================================================

(defn get-mutuals
  "Get mutual connections on Partiful"
  []
  (api-request {:endpoint "/getMutuals"}))

(defn get-my-rsvps
  "Get all events user has RSVPed to (invites/attended)"
  []
  (api-request {:endpoint "/getMyRsvps"}))

(defn get-users
  "Get user profiles by IDs"
  [user-ids]
  (let [{:keys [user-id]} (load-config)]
    (api-request {:endpoint "/getUsers"
                  :body {:data {:params {:ids user-ids
                                         :excludePartyStats false
                                         :includePartyStats true}
                                :userId user-id}}})))

(defn get-event
  "Get event details by ID"
  [event-id]
  (api-request {:endpoint "/getEvent"
                :params {:eventId event-id}}))

(defn get-hosted-events
  "Get events the user is hosting"
  []
  (api-request {:endpoint "/getHostedEvents"}))

(defn get-invitable-contacts
  "Get contacts that can be invited to an event"
  [event-id & {:keys [skip limit] :or {skip 0 limit 100}}]
  (api-request {:endpoint "/getInvitableContacts"
                :params {:eventId event-id
                         :skip skip
                         :limit limit}}))

;; ============================================================
;; Playwright Auth Extraction
;; ============================================================

(def playwright-script
  "const { chromium } = require('playwright');

async function extractPartifulAuth() {
  const browser = await chromium.launch({ headless: false });
  const context = await browser.newContext();
  const page = await context.newPage();

  let authToken = null;
  let userId = null;

  // Intercept network requests to capture auth
  page.on('request', request => {
    const auth = request.headers()['authorization'];
    if (auth && auth.startsWith('Bearer ')) {
      authToken = auth.replace('Bearer ', '');
    }
  });

  page.on('response', async response => {
    const url = response.url();
    if (url.includes('partiful.com') && !userId) {
      try {
        const json = await response.json();
        if (json.userId) userId = json.userId;
        if (json.user?.id) userId = json.user.id;
      } catch {}
    }
  });

  await page.goto('https://partiful.com/login');
  console.log('Please log in to Partiful in the browser window...');
  console.log('The window will close automatically after detecting auth.');

  // Wait for navigation after login
  await page.waitForURL('**/home**', { timeout: 120000 });

  // Give time to capture requests
  await page.waitForTimeout(3000);

  // Try to get user ID from profile if not captured
  if (!userId) {
    await page.goto('https://partiful.com/profile');
    await page.waitForTimeout(2000);
    const url = page.url();
    const match = url.match(/\\/u\\/([^/?]+)/);
    if (match) userId = match[1];
  }

  await browser.close();

  return { authToken, userId };
}

extractPartifulAuth()
  .then(result => console.log(JSON.stringify(result)))
  .catch(err => console.error('Error:', err.message));
")

(defn extract-auth-playwright []
  (println "Launching Playwright to extract Partiful auth...")
  (println "A browser window will open. Please log in to Partiful.")

  ;; Check if playwright is installed
  (let [check (shell {:out :string :err :string :continue true}
                     "npx playwright --version")]
    (when (not= 0 (:exit check))
      (println "Installing Playwright...")
      (shell "npm install -g playwright")
      (shell "npx playwright install chromium")))

  ;; Write temp script
  (let [script-file "/tmp/partiful-auth.js"]
    (spit script-file playwright-script)
    (let [result (shell {:out :string :err :string}
                        "node" script-file)
          output (str/trim (:out result))]
      ;; Parse the JSON output (last line)
      (when-let [json-line (last (str/split-lines output))]
        (try
          (let [auth (json/parse-string json-line true)]
            (when (and (:authToken auth) (:userId auth))
              (save-config {:auth-token (:authToken auth)
                           :user-id (:userId auth)})
              (println "Auth extracted successfully!")
              (println "User ID:" (:userId auth))
              (println "Note: Set PARTIFUL_FIREBASE_API_KEY env var for token refresh")
              auth))
          (catch Exception e
            (println "Failed to parse auth:" (.getMessage e))
            (println "Raw output:" output)))))))

;; ============================================================
;; Display Helpers
;; ============================================================

(defn format-date [date-str]
  (when date-str
    (-> date-str
        (str/replace "T" " ")
        (str/split #"\.")
        first
        (subs 0 10))))  ; Just date part

(defn format-rsvp-status [status]
  (case status
    "going" "GOING"
    "maybe" "MAYBE"
    "notGoing" "NOT GOING"
    "invited" "INVITED"
    (or status "?")))

(defn print-event [event]
  (println "----------------------------------------")
  (println "Event:" (:title event (:name event)))
  (println "  ID:" (:eventId event (:id event)))
  (println "  Date:" (format-date (:startTime event (:startDate event))))
  (when-let [status (:rsvpStatus event)]
    (println "  RSVP:" (format-rsvp-status status)))
  (when-let [loc (:locationDisplayText event (:location event))]
    (println "  Location:" loc))
  (when-let [desc (:description event)]
    (when (seq desc)
      (println "  Description:" (subs desc 0 (min 80 (count desc))))))
  (println "  URL: https://partiful.com/e/" (:eventId event (:id event))))

(defn print-rsvp-row [rsvp]
  (let [date (format-date (:startTime rsvp))
        status (format-rsvp-status (:rsvpStatus rsvp))
        title (:title rsvp)
        event-id (:eventId rsvp)]
    (printf "%s | %-9s | %s | https://partiful.com/e/%s%n"
            date status title event-id)))

(defn print-user [user]
  (println "  -" (:name user (:displayName user))
           (when (:username user) (str "(@" (:username user) ")"))))

;; ============================================================
;; CLI Commands
;; ============================================================

(defn cmd-auth [_]
  (extract-auth-playwright))

(defn cmd-mutuals [_]
  (println "Fetching mutuals...")
  (try
    (let [resp (get-mutuals)
          mutuals (or (:result resp) (:mutuals resp) (:data resp))]
      (println "\nYour Partiful Mutuals:")
      (if (seq mutuals)
        (doseq [m mutuals]
          (print-user m))
        (println "  No mutuals found.")))
    (catch Exception e
      (println "Error fetching mutuals:" (.getMessage e)))))

(defn cmd-invites [_]
  (println "Fetching your RSVPs and invites...")
  (try
    (let [resp (get-my-rsvps)
          ;; Navigate: result -> data -> events
          events (get-in resp [:result :data :events] [])
          sorted-events (sort-by :startDate events)]
      (println "\nYour Partiful Events:")
      (println (str/join "" (repeat 90 "-")))
      (printf "%-10s | %-9s | %-45s | %s%n" "DATE" "RSVP" "EVENT" "ID")
      (println (str/join "" (repeat 90 "-")))
      (doseq [event sorted-events]
        (let [date (some-> (:startDate event) (subs 0 10))
              status (or (get-in event [:guest :status]) "?")
              title (or (:title event) "Untitled")
              title-short (if (> (count title) 45) (str (subs title 0 42) "...") title)
              event-id (:id event)]
          (printf "%-10s | %-9s | %-45s | %s%n"
                  (or date "TBD")
                  status
                  title-short
                  event-id)))
      (println (str/join "" (repeat 90 "-")))
      (println "Total:" (count events) "events"))
    (catch Exception e
      (println "Error fetching invites:" (.getMessage e))
      (println "Make sure your auth token is valid. Run: bb partiful.clj auth"))))

(defn cmd-events [_]
  (println "Fetching your hosted events...")
  (try
    (let [resp (get-hosted-events)
          events (or (:result resp) (:events resp) (:data resp))]
      (println "\nYour Hosted Events:")
      (if (seq events)
        (doseq [event events]
          (print-event event))
        (println "  No hosted events found.")))
    (catch Exception e
      (println "Error fetching events:" (.getMessage e)))))

(defn cmd-event [[event-id]]
  (if event-id
    (do
      (println "Fetching event" event-id "...")
      (try
        (let [event (get-event event-id)]
          (print-event (or (:result event) event))
          (println "\nFull data:")
          (println (json/generate-string event {:pretty true})))
        (catch Exception e
          (println "Error:" (.getMessage e)))))
    (println "Usage: bb partiful.clj event <event-id>")))

(defn cmd-help [_]
  (println "Partiful CLI - Access your Partiful data")
  (println "")
  (println "Commands:")
  (println "  auth      - Extract auth token via Playwright browser login")
  (println "  invites   - List events you're invited to")
  (println "  events    - List events you're hosting")
  (println "  mutuals   - List your mutual connections")
  (println "  event <id> - Get details for specific event")
  (println "  help      - Show this help")
  (println "")
  (println "Environment variables:")
  (println "  PARTIFUL_AUTH_TOKEN      - Firebase auth token")
  (println "  PARTIFUL_USER_ID         - Your Partiful user ID")
  (println "  PARTIFUL_REFRESH_TOKEN   - For auto-refreshing expired tokens")
  (println "  PARTIFUL_FIREBASE_API_KEY - Firebase API key (from Partiful web app)")
  (println "")
  (println "First run: bb partiful.clj auth"))

;; ============================================================
;; Main
;; ============================================================

(def commands
  {"auth" cmd-auth
   "invites" cmd-invites
   "events" cmd-events
   "mutuals" cmd-mutuals
   "event" cmd-event
   "help" cmd-help})

(defn -main [& args]
  (let [cmd (or (first args) "help")
        cmd-fn (get commands cmd cmd-help)]
    (cmd-fn (rest args))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
