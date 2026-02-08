---
name: delta-derivation
description: Extract information delta between Claude.ai conversation exports using ACSets morphisms and bisimulation verification
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Delta Derivation Skill

**Trit**: -1 (MINUS - Validator)
**Color**: #007FFF (Cold Blue)
**Role**: Extract and verify conversation export deltas

---

## Core Algorithm

```bash
# 1. Extract conversations from exports
unzip -o "$RECENT_ZIP" conversations.json -d /tmp/recent_export
unzip -o "$PREVIOUS_ZIP" conversations.json -d /tmp/previous_export

# 2. Extract conversation IDs
jq -r '.[].conversation_id' /tmp/recent_export/conversations.json | sort > /tmp/recent_ids.txt
jq -r '.[].conversation_id' /tmp/previous_export/conversations.json | sort > /tmp/prev_ids.txt

# 3. Compute delta (new conversations)
comm -23 /tmp/recent_ids.txt /tmp/prev_ids.txt > /tmp/new_ids.txt

# 4. Bisimulation check (mutations in shared conversations)
jq -r '.[] | "\(.conversation_id) \(.current_node)"' /tmp/recent_export/conversations.json | sort > /tmp/recent_states.txt
jq -r '.[] | "\(.conversation_id) \(.current_node)"' /tmp/previous_export/conversations.json | sort > /tmp/prev_states.txt
comm -3 /tmp/recent_states.txt /tmp/prev_states.txt > /tmp/mutated.txt
```

---

## ACSets Schema

```clojure
(def ConversationACSet
  {:objects #{:Conversation :Message :Node}
   :morphisms {:has_mapping [:Conversation :Node]
               :parent_of [:Node :Node]
               :contains [:Node :Message]}
   :attributes {:conversation_id [:Conversation :String]
                :title [:Conversation :String]
                :create_time [:Conversation :Timestamp]
                :update_time [:Conversation :Timestamp]
                :current_node [:Conversation :UUID]}})

(defn delta-morphism [recent previous]
  "Compute injective morphism from previous → recent"
  (let [shared (set/intersection (ids recent) (ids previous))
        new-convos (set/difference (ids recent) (ids previous))
        removed (set/difference (ids previous) (ids recent))]
    {:type :injection
     :shared (count shared)
     :new (count new-convos)
     :removed (count removed)
     :new-ids new-convos}))
```

---

## Bi