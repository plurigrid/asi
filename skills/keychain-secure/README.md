# Keychain Secure Skill

> *"macOS Keychain with GF(3) balanced operations. Store, retrieve, delete in triads."*

## Overview

**Keychain Secure** provides credential management through macOS Keychain with GF(3)-balanced operations. Every store (+1) must eventually be matched by a delete (-1).

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | 0 (ERGODIC) |
| Role | COORDINATOR |
| Function | Coordinates credential lifecycle |

## Operations

| Operation | Trit | GF(3) Role |
|-----------|------|------------|
| `store` | +1 | GENERATOR |
| `retrieve` | 0 | COORDINATOR |
| `delete` | -1 | VALIDATOR |

## Core Interface

```bash
# Store credential (+1 GENERATOR)
security add-generic-password \
  -a "$USER" \
  -s "service-name" \
  -w "secret-value" \
  -T "" \
  keychain.keychain

# Retrieve credential (0 COORDINATOR)
security find-generic-password \
  -a "$USER" \
  -s "service-name" \
  -w \
  keychain.keychain

# Delete credential (-1 VALIDATOR)
security delete-generic-password \
  -a "$USER" \
  -s "service-name" \
  keychain.keychain
```

## Babashka Integration

```clojure
(ns keychain.secure
  (:require [babashka.process :refer [shell]]))

(defn store-credential
  "Store credential in Keychain (+1 GENERATOR)"
  [service account password]
  (shell "security" "add-generic-password"
         "-a" account
         "-s" service
         "-w" password
         "-U"))  ; Update if exists

(defn retrieve-credential
  "Retrieve credential from Keychain (0 COORDINATOR)"
  [service account]
  (-> (shell {:out :string}
             "security" "find-generic-password"
             "-a" account
             "-s" service
             "-w")
      :out
      str/trim))

(defn delete-credential
  "Delete credential from Keychain (-1 VALIDATOR)"
  [service account]
  (shell "security" "delete-generic-password"
         "-a" account
         "-s" service))

(defn gf3-balanced-rotation
  "Rotate credential while maintaining GF(3) balance"
  [service account new-password]
  ;; Store new (+1)
  (store-credential (str service "-new") account new-password)
  ;; Retrieve old (0) - no trit change
  (let [old (retrieve-credential service account)]
    ;; Delete old (-1)
    (delete-credential service account)
    ;; Rename new to current (0)
    ;; Net: +1 + 0 + (-1) = 0 ✓
    {:old old :new new-password :balanced true}))
```

## GF(3) Conservation

```clojure
(defn verify-conservation [operations]
  "Verify GF(3) conservation across operation sequence"
  (let [trit-sum (->> operations
                      (map :trit)
                      (reduce +))]
    {:sum trit-sum
     :conserved (zero? (mod trit-sum 3))}))

;; Example balanced sequence
(def balanced-ops
  [{:op :store   :trit +1 :service "api-key"}
   {:op :retrieve :trit 0  :service "api-key"}
   {:op :delete  :trit -1 :service "api-key"}])

(verify-conservation balanced-ops)
;; => {:sum 0, :conserved true}
```

## Secure Patterns

### API Key Rotation

```clojure
(defn rotate-api-key [service]
  (let [new-key (generate-api-key)]
    ;; Balanced rotation
    (store-credential (str service "-pending") "api" new-key)  ; +1
    (retrieve-credential service "api")                         ; 0
    (delete-credential service "api")                           ; -1
    (store-credential service "api" new-key)                    ; +1
    (delete-credential (str service "-pending") "api")          ; -1
    ;; Net: +1 + 0 + (-1) + (+1) + (-1) = 0 ✓
    new-key))
```

### OAuth Token Management

```clojure
(defn oauth-token-lifecycle [provider]
  {:store    (fn [token] (store-credential provider "oauth" token))
   :refresh  (fn [] (retrieve-credential provider "oauth"))
   :revoke   (fn [] (delete-credential provider "oauth"))
   :gf3-sum  0})  ; Lifecycle is balanced
```

## GF(3) Triads

```
keychain-secure (0) ⊗ credential-generator (+1) ⊗ secret-validator (-1) = 0 ✓
keychain-secure (0) ⊗ aptos-gf3-society (+1) ⊗ merkle-validation (-1) = 0 ✓
```

---

**Skill Name**: keychain-secure
**Type**: Credential Management
**Trit**: 0 (ERGODIC - COORDINATOR)
**GF(3)**: Balanced store/retrieve/delete operations
