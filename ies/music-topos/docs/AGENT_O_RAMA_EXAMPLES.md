# Agent-o-rama HTTP Client Usage Examples

## Table of Contents
- [Basic Agent Invocation](#basic-agent-invocation)
- [Streaming Responses](#streaming-responses)
- [Training Data Submission](#training-data-submission)
- [Model Inference](#model-inference)
- [Pattern Extraction](#pattern-extraction)
- [Advanced Patterns](#advanced-patterns)

## Basic Agent Invocation

### Synchronous Invocation

```bash
# Invoke an agent and wait for result
curl -X POST http://localhost:3000/api/agents/com.example.TextModule/AnalysisAgent/invoke \
  -H "Content-Type: application/json" \
  -d '{
    "input": "Analyze this text for sentiment and key topics",
    "metadata": {
      "user-id": "user-123",
      "session-id": "session-456"
    }
  }'
```

Response:
```json
{
  "invoke-id": "550e8400-e29b-41d4-a716-446655440000",
  "result": {
    "sentiment": "positive",
    "topics": ["technology", "innovation"],
    "confidence": 0.92
  },
  "status": "completed",
  "duration-ms": 1234
}
```

### Asynchronous Invocation

```bash
# Invoke asynchronously and get invoke-id
curl -X POST http://localhost:3000/api/agents/com.example.TextModule/AnalysisAgent/invoke \
  -H "Content-Type: application/json" \
  -d '{
    "input": "Process large document...",
    "async?": true
  }'
```

Response:
```json
{
  "invoke-id": "550e8400-e29b-41d4-a716-446655440000",
  "status": "initiated"
}
```

### Check Invocation Status

```bash
# Poll for results
curl http://localhost:3000/api/agents/com.example.TextModule/AnalysisAgent/invokes/550e8400-e29b-41d4-a716-446655440000
```

Response:
```json
{
  "invoke-id": "550e8400-e29b-41d4-a716-446655440000",
  "status": "completed",
  "started": 1703188800000,
  "completed": 1703188801234,
  "result": {...},
  "duration-ms": 1234
}
```

## Streaming Responses

### Server-Sent Events (SSE)

```bash
# Stream agent output in real-time
curl -N http://localhost:3000/api/agents/com.example.TextModule/WriterAgent/stream \
  -H "Content-Type: application/json" \
  -d '{
    "input": "Write a summary of quantum computing",
    "node": "generate"
  }'
```

Response (SSE stream):
```
data: {"type":"chunk","content":"Quantum computing"}

data: {"type":"chunk","content":" leverages principles"}

data: {"type":"chunk","content":" of quantum mechanics..."}

data: {"type":"complete","result":"Quantum computing leverages principles of quantum mechanics..."}
```

### Clojure Client

```clojure
(require '[clj-http.client :as http])
(require '[cheshire.core :as json])

(defn stream-agent-output [module agent input node callback]
  (let [url (str "http://localhost:3000/api/agents/" module "/" agent "/stream")
        response (http/post url
                           {:body (json/generate-string {:input input :node node})
                            :headers {"Content-Type" "application/json"}
                            :as :stream})]

    (with-open [reader (clojure.java.io/reader (:body response))]
      (doseq [line (line-seq reader)]
        (when (.startsWith line "data: ")
          (let [data (json/parse-string (subs line 6) true)]
            (callback data)))))))

;; Usage
(stream-agent-output "com.example.TextModule" "WriterAgent"
                     "Explain neural networks"
                     "generate"
                     (fn [chunk]
                       (println "Received:" (:content chunk))))
```

## Training Data Submission

### Submit Training Examples

```bash
curl -X POST http://localhost:3000/api/training/submit \
  -H "Content-Type: application/json" \
  -d '{
    "data": {
      "dataset-name": "sentiment-training-v1",
      "examples": [
        {
          "input": "This product is amazing!",
          "output": {"sentiment": "positive", "score": 0.95},
          "metadata": {"source": "manual", "verified": true}
        },
        {
          "input": "Disappointed with the quality",
          "output": {"sentiment": "negative", "score": 0.87},
          "metadata": {"source": "manual", "verified": true}
        }
      ]
    }
  }'
```

Response:
```json
{
  "status": "success",
  "dataset": "sentiment-training-v1",
  "examples-count": 2,
  "message": "Training data submitted successfully"
}
```

### Batch Upload from File

```clojure
(defn upload-training-data [dataset-name examples-file]
  (let [examples (json/parse-string (slurp examples-file) true)
        url "http://localhost:3000/api/training/submit"
        payload {:data {:dataset-name dataset-name
                       :examples examples}}]

    (http/post url
              {:body (json/generate-string payload)
               :headers {"Content-Type" "application/json"}})))

;; Usage
(upload-training-data "sentiment-v2" "training-examples.json")
```

## Model Inference

### Standard Inference

```bash
curl -X POST http://localhost:3000/api/inference \
  -H "Content-Type: application/json" \
  -d '{
    "input": {
      "text": "Classify this customer review",
      "context": {"product-category": "electronics"}
    },
    "options": {
      "model": "gpt-4",
      "temperature": 0.7,
      "max-tokens": 150
    }
  }'
```

Response:
```json
{
  "status": "success",
  "result": {
    "prediction": "positive",
    "confidence": 0.95,
    "reasoning": "Customer expresses satisfaction..."
  },
  "model": "gpt-4",
  "duration-ms": 342
}
```

### Batch Inference

```clojure
(defn batch-inference [inputs model-opts]
  (pmap (fn [input]
          (http/post "http://localhost:3000/api/inference"
                    {:body (json/generate-string
                            {:input input
                             :options model-opts})
                     :headers {"Content-Type" "application/json"}}))
        inputs))

;; Usage
(def results
  (batch-inference
    [{:text "Review 1..."} {:text "Review 2..."}]
    {:model "gpt-4" :temperature 0.5}))
```

## Pattern Extraction

### Extract Sequential Patterns

```bash
curl -X POST http://localhost:3000/api/patterns/extract \
  -H "Content-Type: application/json" \
  -d '{
    "source": {
      "dataset": "user-sessions-2024",
      "filters": {
        "min-confidence": 0.8,
        "min-support": 100
      }
    },
    "options": {
      "pattern-type": "sequential"
    }
  }'
```

Response:
```json
{
  "status": "success",
  "patterns": [
    {
      "type": "sequential",
      "pattern": ["view_product", "add_to_cart", "checkout"],
      "frequency": 1542,
      "confidence": 0.88
    },
    {
      "type": "sequential",
      "pattern": ["search", "view_product", "compare"],
      "frequency": 987,
      "confidence": 0.82
    }
  ],
  "dataset": "user-sessions-2024"
}
```

### Extract Structural Patterns

```bash
curl -X POST http://localhost:3000/api/patterns/extract \
  -H "Content-Type: application/json" \
  -d '{
    "source": {
      "dataset": "code-samples",
      "filters": {
        "min-confidence": 0.75
      }
    },
    "options": {
      "pattern-type": "structural"
    }
  }'
```

## Advanced Patterns

### Chained Agent Calls

```clojure
(defn analyze-and-summarize [text]
  ;; Step 1: Analyze
  (let [analysis-result
        (-> (http/post "http://localhost:3000/api/agents/com.example/AnalysisAgent/invoke"
                      {:body (json/generate-string {:input text})
                       :headers {"Content-Type" "application/json"}})
            :body
            (json/parse-string true)
            :result)

        ;; Step 2: Summarize based on analysis
        summary-result
        (-> (http/post "http://localhost:3000/api/agents/com.example/SummaryAgent/invoke"
                      {:body (json/generate-string
                              {:input text
                               :metadata {:analysis analysis-result}})
                       :headers {"Content-Type" "application/json"}})
            :body
            (json/parse-string true)
            :result)]

    {:analysis analysis-result
     :summary summary-result}))
```

### Parallel Agent Invocations

```clojure
(require '[clojure.core.async :as async])

(defn parallel-agent-invoke [agents input]
  (let [results-ch (async/chan (count agents))]

    ;; Launch all agents in parallel
    (doseq [[module agent] agents]
      (async/go
        (let [result
              (-> (http/post
                    (str "http://localhost:3000/api/agents/" module "/" agent "/invoke")
                    {:body (json/generate-string {:input input})
                     :headers {"Content-Type" "application/json"}})
                  :body
                  (json/parse-string true))]
          (async/>! results-ch [agent result]))))

    ;; Collect results
    (into {}
          (repeatedly (count agents)
                     #(async/<!! results-ch)))))

;; Usage
(def results
  (parallel-agent-invoke
    [["com.example.Module1" "SentimentAgent"]
     ["com.example.Module2" "TopicAgent"]
     ["com.example.Module3" "EntityAgent"]]
    "Analyze this text from multiple perspectives"))
```

### Error Handling

```clojure
(defn invoke-with-retry [module agent input max-retries]
  (loop [attempt 1]
    (try
      (let [response
            (http/post
              (str "http://localhost:3000/api/agents/" module "/" agent "/invoke")
              {:body (json/generate-string {:input input})
               :headers {"Content-Type" "application/json"}
               :throw-exceptions false})]

        (if (= 200 (:status response))
          (json/parse-string (:body response) true)

          (if (< attempt max-retries)
            (do
              (Thread/sleep (* 1000 attempt)) ; Exponential backoff
              (recur (inc attempt)))

            (throw (ex-info "Max retries exceeded"
                           {:status (:status response)
                            :body (:body response)})))))

      (catch Exception e
        (if (< attempt max-retries)
          (do
            (Thread/sleep (* 1000 attempt))
            (recur (inc attempt)))
          (throw e))))))
```

### Streaming with Backpressure

```clojure
(require '[manifold.stream :as s])
(require '[manifold.deferred :as d])

(defn stream-with-backpressure [module agent input node buffer-size]
  (let [stream (s/stream buffer-size)]

    (d/future
      (try
        (let [response
              (http/post
                (str "http://localhost:3000/api/agents/" module "/" agent "/stream")
                {:body (json/generate-string {:input input :node node})
                 :headers {"Content-Type" "application/json"}
                 :as :stream})]

          (with-open [reader (clojure.java.io/reader (:body response))]
            (doseq [line (line-seq reader)]
              (when (.startsWith line "data: ")
                (let [data (json/parse-string (subs line 6) true)]
                  @(s/put! stream data))))))

        (catch Exception e
          @(s/put! stream {:type "error" :message (.getMessage e)}))

        (finally
          (s/close! stream))))

    stream))

;; Usage
(let [stream (stream-with-backpressure
               "com.example" "WriterAgent"
               "Generate long text" "generate" 10)]

  (s/consume
    (fn [chunk]
      (when (= "chunk" (:type chunk))
        (print (:content chunk))
        (flush)))
    stream))
```

## Testing Examples

### Integration Test

```clojure
(ns agents.agent-o-rama-http-client-test
  (:require [clojure.test :refer :all]
            [agents.agent-o-rama-http-client :as client]
            [clj-http.client :as http]
            [cheshire.core :as json]))

(deftest test-agent-invocation
  (testing "Synchronous agent invocation"
    (let [server (client/start-http-service {:port 3001})
          response (http/post "http://localhost:3001/api/agents/test/TestAgent/invoke"
                             {:body (json/generate-string {:input "test"})
                              :headers {"Content-Type" "application/json"}})
          result (json/parse-string (:body response) true)]

      (is (= 200 (:status response)))
      (is (= "completed" (:status result)))
      (is (contains? result :invoke-id))
      (is (contains? result :result))

      (client/stop-http-service server))))

(deftest test-health-check
  (testing "Health check endpoint"
    (let [server (client/start-http-service {:port 3002})
          response (http/get "http://localhost:3002/health")
          result (json/parse-string (:body response) true)]

      (is (= 200 (:status response)))
      (is (= "healthy" (:status result)))

      (client/stop-http-service server))))
```

## Performance Considerations

### Connection Pooling

```clojure
(def http-client
  (http/build-http-client
    {:connection-pool {:threads 10
                      :default-per-route 5
                      :insecure? false
                      :timeout 30000}}))

(defn invoke-with-pooling [module agent input]
  (http/post
    (str "http://localhost:3000/api/agents/" module "/" agent "/invoke")
    {:body (json/generate-string {:input input})
     :headers {"Content-Type" "application/json"}
     :http-client http-client}))
```

### Request Batching

```clojure
(defn batch-requests [requests batch-size]
  (->> requests
       (partition-all batch-size)
       (mapcat (fn [batch]
                 (let [futures (mapv #(future (invoke-agent %)) batch)]
                   (mapv deref futures))))))
```
