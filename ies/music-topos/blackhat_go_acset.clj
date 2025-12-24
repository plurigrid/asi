;; BlackHat Go ACSet Model - ananas.clj
;; Structured attack knowledge from BlackHat Go book
;; Chapter-based technique hierarchy with side-channel relationships

(ns blackhat-go.acset
  (:require [ananas.core :as acset]
            [ananas.categorical :as cat]))

;; ============================================================================
;; SCHEMA DEFINITION: Complete BlackHat Go Knowledge Graph
;; ============================================================================

(def BlackHatGoSchema
  {:Technique
   {:id :ID
    :name :String
    :chapter :Int
    :complexity :String  ; Beginner, Intermediate, Advanced
    :risk_level :Int     ; 1-10 scale
    :prerequisites [:String]
    :tools [:String]
    :description :String
    :discovered_year :Int
    :affected_systems [:String]}

   :SideChannel
   {:id :ID
    :type :String        ; Power, Thermal, EM, Timing, Acoustic, Optical, Fault
    :frequency_hz :Int
    :measurable_by [:String]
    :signal_strength :String  ; Weak, Medium, Strong
    :noise_floor :Float
    :snr_ratio :Float}

   :Exploitation
   {:technique :Technique
    :sidechannel :SideChannel
    :detection_difficulty :String
    :theoretical_accuracy :Float
    :practical_accuracy :Float
    :attack_complexity :String
    :required_access :String}  ; Local, Network, Physical

   :Defense
   {:id :ID
    :name :String
    :mitigates [:Technique]
    :implementation_cost :String
    :effectiveness :Float
    :performance_penalty :Float
    :deployment_difficulty :String
    :requires_hardware_change :Boolean}

   :Chapter
   {:id :Int
    :title :String
    :techniques [:Technique]
    :main_concepts [:String]
    :learning_objectives [:String]
    :lab_exercises [:String]}

   :Vulnerability
   {:id :ID
    :technique :Technique
    :affected_processor :String
    :affected_os [:String]
    :cve_ids [:String]
    :discoverer :String
    :discovery_date :Int
    :public_disclosure :Int}})

;; ============================================================================
;; CHAPTER 1: INTRODUCTION & BACKGROUND
;; ============================================================================

(def Chapter1Data
  {:Chapter
   {:id 1
    :title "Introduction to Microarchitecture & Side Channels"
    :main_concepts ["CPU architecture" "Pipeline execution" "Cache organization"
                   "Side-channel concept" "Attack taxonomy"]
    :learning_objectives ["Understand CPU fundamentals"
                         "Learn side-channel classification"
                         "Recognize threat models"
                         "Understand attack prerequisites"]}

   :Techniques
   [{:id "intro-cpu-architecture"
     :name "CPU Architecture Fundamentals"
     :chapter 1
     :complexity "Beginner"
     :risk_level 0
     :description "CPU pipelines, instruction execution, caches, branch predictors"}

    {:id "intro-side-channels"
     :name "Side-Channel Attack Introduction"
     :chapter 1
     :complexity "Beginner"
     :risk_level 1
     :description "Classification and overview of all side-channel attack types"}

    {:id "intro-threat-models"
     :name "Threat Models for Side-Channels"
     :chapter 1
     :complexity "Intermediate"
     :risk_level 2
     :description "Adversary capabilities, assumptions, and realistic scenarios"}]})

;; ============================================================================
;; CHAPTER 2: MICROARCHITECTURE & MEMORY SYSTEMS
;; ============================================================================

(def Chapter2Data
  {:Chapter
   {:id 2
    :title "Microarchitecture & Memory Hierarchy"
    :main_concepts ["Cache hierarchy" "Cache coherence" "Memory ordering"
                   "TLB (Translation Lookaside Buffer)" "DRAM architecture"
                   "Branch prediction" "Prefetching"]
    :learning_objectives ["Deep dive into cache architecture"
                         "Understand memory timing"
                         "Learn about shared CPU resources"
                         "Recognize information leakage opportunities"]}

   :Techniques
   [{:id "cache-l1-l2-l3"
     :name "CPU Cache Hierarchy (L1/L2/L3)"
     :chapter 2
     :complexity "Intermediate"
     :risk_level 3
     :description "Cache organization, replacement policies (LRU), coherence protocols"
     :prerequisites ["intro-cpu-architecture"]
     :tools ["perf" "cachegrind" "Intel VTune"]}

    {:id "cache-replacement-policy"
     :name "Cache Replacement Policy Analysis"
     :chapter 2
     :complexity "Intermediate"
     :risk_level 4
     :description "Exploit LRU/pseudo-LRU replacement decisions"
     :prerequisites ["cache-l1-l2-l3"]}

    {:id "tlb-side-channel"
     :name "TLB Side-Channel Analysis"
     :chapter 2
     :complexity "Intermediate"
     :risk_level 5
     :description "TLB entries leak virtual address patterns"
     :prerequisites ["intro-cpu-architecture"]
     :tools ["custom-timing-code" "perf"]}

    {:id "branch-prediction"
     :name "Branch Predictor Analysis"
     :chapter 2
     :complexity "Intermediate"
     :risk_level 4
     :description "Infer branch outcomes through timing analysis"
     :prerequisites ["intro-cpu-architecture"]
     :tools ["timing-measurement"]}

    {:id "dram-rowhammer"
     :name "DRAM Row Hammer Attack"
     :chapter 2
     :complexity "Advanced"
     :risk_level 8
     :description "Exploit DRAM refresh mechanisms to flip memory bits"
     :prerequisites ["cache-l1-l2-l3"]
     :tools ["custom-memory-code" "rowhammer-tools"]
     :discovered_year 2014
     :affected_systems ["All modern x86" "ARM processors"]}

    {:id "memory-hierarchy-timing"
     :name "Memory Hierarchy Timing Leaks"
     :chapter 2
     :complexity "Intermediate"
     :risk_level 5
     :description "Measure access times at different cache levels"
     :prerequisites ["cache-l1-l2-l3"]}]})

;; ============================================================================
;; CHAPTER 3: SPECULATIVE EXECUTION
;; ============================================================================

(def Chapter3Data
  {:Chapter
   {:id 3
    :title "Speculative Execution & Transient Attacks"
    :main_concepts ["Speculative execution" "Transient faults" "Spectre" "Meltdown"
                   "Return-Oriented Programming" "Gadget chains"]
    :learning_objectives ["Understand speculative execution in modern CPUs"
                         "Learn about transient-execution attacks"
                         "Understand Spectre variants"
                         "Learn Meltdown attack mechanics"
                         "Understand exploitation techniques"]}

   :Techniques
   [{:id "spectre-v1"
     :name "Spectre v1 (Bounds Check Bypass)"
     :chapter 3
     :complexity "Advanced"
     :risk_level 10
     :description "Bypass bounds checks via speculative execution to leak data"
     :prerequisites ["intro-cpu-architecture" "branch-prediction"]
     :tools ["custom-poc" "kernel-access"]
     :discovered_year 2017
     :affected_systems ["Intel" "AMD" "ARM" "All modern CPUs"]
     :cve_ids ["CVE-2017-5753"]}

    {:id "spectre-v2"
     :name "Spectre v2 (Branch Target Injection)"
     :chapter 3
     :complexity "Advanced"
     :risk_level 10
     :description "Poison branch prediction buffer (BTB) to redirect indirect branches"
     :prerequisites ["branch-prediction"]
     :tools ["kernel-gadgets" "IBPB-bypass"]
     :discovered_year 2017
     :affected_systems ["Intel" "AMD"]
     :cve_ids ["CVE-2017-5715"]}

    {:id "meltdown"
     :name "Meltdown (Rogue Data Cache Load)"
     :chapter 3
     :complexity "Advanced"
     :risk_level 10
     :description "Read arbitrary kernel memory via exception handling race condition"
     :prerequisites ["intro-cpu-architecture"]
     :tools ["custom-poc" "kernel-gadgets"]
     :discovered_year 2017
     :affected_systems ["Intel (mainly)"]
     :cve_ids ["CVE-2017-5754"]}

    {:id "rogue-system-register"
     :name "Rogue System Register Read"
     :chapter 3
     :complexity "Advanced"
     :risk_level 9
     :description "Read privileged system registers through speculative execution"
     :prerequisites ["spectre-v1"]}

    {:id "spectre-pht-poison"
     :name "Pattern History Table (PHT) Poisoning"
     :chapter 3
     :complexity "Advanced"
     :risk_level 9
     :description "Poison PHT entries to control speculative execution"
     :prerequisites ["branch-prediction"]}

    {:id "indirect-branch-prediction"
     :name "Indirect Branch Prediction Poisoning"
     :chapter 3
     :complexity "Advanced"
     :risk_level 9
     :description "Exploit indirect branch misprediction for information leakage"
     :prerequisites ["spectre-v2"]}

    {:id "return-oriented-programming"
     :name "Return-Oriented Programming (ROP)"
     :chapter 3
     :complexity "Advanced"
     :risk_level 9
     :description "Chain gadgets to execute arbitrary code via speculative execution"
     :prerequisites ["spectre-v1"]}]})

;; ============================================================================
;; CHAPTER 4: POWER ANALYSIS ATTACKS
;; ============================================================================

(def Chapter4Data
  {:Chapter
   {:id 4
    :title "Power Analysis Attacks"
    :main_concepts ["Power consumption patterns" "Statistical analysis" "Correlation"
                   "Template attacks" "Masking" "Hiding countermeasures"]
    :learning_objectives ["Understand power consumption models"
                         "Learn statistical analysis techniques"
                         "Understand CPA/DPA attacks"
                         "Learn about power analysis countermeasures"]}

   :Techniques
   [{:id "simple-power-analysis"
     :name "Simple Power Analysis (SPA)"
     :chapter 4
     :complexity "Intermediate"
     :risk_level 6
     :description "Visual inspection of power traces to identify operations"
     :prerequisites ["intro-cpu-architecture"]
     :tools ["oscilloscope" "powermetrics"]}

    {:id "differential-power-analysis"
     :name "Differential Power Analysis (DPA)"
     :chapter 4
     :complexity "Advanced"
     :risk_level 8
     :description "Statistical analysis of power differences to extract keys"
     :prerequisites ["simple-power-analysis"]
     :tools ["Python" "NumPy" "SciPy"]
     :discovered_year 1998}

    {:id "correlation-power-analysis"
     :name "Correlation Power Analysis (CPA)"
     :chapter 4
     :complexity "Advanced"
     :risk_level 9
     :description "Correlate power with key hypotheses to recover AES/RSA keys"
     :prerequisites ["differential-power-analysis"]
     :tools ["ChipWhisperer" "Python"]
     :discovered_year 2004}

    {:id "mutual-information-analysis"
     :name "Mutual Information Analysis (MIA)"
     :chapter 4
     :complexity "Advanced"
     :risk_level 9
     :description "Information-theoretic power analysis attack"
     :prerequisites ["correlation-power-analysis"]}

    {:id "stochastic-models"
     :name "Stochastic Models for Power Analysis"
     :chapter 4
     :complexity "Advanced"
     :risk_level 9
     :description "Model power consumption stochastically for attacks"
     :prerequisites ["correlation-power-analysis"]}

    {:id "template-attacks"
     :name "Template Attacks (Profiling)"
     :chapter 4
     :complexity "Advanced"
     :risk_level 9
     :description "Build templates via machine learning on power traces"
     :prerequisites ["correlation-power-analysis"]
     :tools ["scikit-learn" "TensorFlow"]}

    {:id "power-analysis-masking"
     :name "Power Masking (Countermeasure)"
     :chapter 4
     :complexity "Advanced"
     :risk_level 7
     :description "Add noise to power consumption to hide operations"
     :prerequisites ["simple-power-analysis"]}

    {:id "random-delay"
     :name "Random Delays (Countermeasure)"
     :chapter 4
     :complexity "Intermediate"
     :risk_level 5
     :description "Randomize execution time to desynchronize traces"
     :prerequisites ["simple-power-analysis"]}]})

;; ============================================================================
;; CHAPTER 5: TIMING ATTACKS
;; ============================================================================

(def Chapter5Data
  {:Chapter
   {:id 5
    :title "Timing Side-Channels & Cache Attacks"
    :main_concepts ["Timing leaks" "Cache-timing attacks" "Flush+Reload"
                   "Prime+Probe" "Evict+Time" "Constant-time coding"]
    :learning_objectives ["Understand timing vulnerabilities"
                         "Learn cache-timing attacks"
                         "Understand practical exploits"
                         "Learn constant-time implementations"]}

   :Techniques
   [{:id "timing-attack-basic"
     :name "Timing Attack on Cryptographic Operations"
     :chapter 5
     :complexity "Intermediate"
     :risk_level 7
     :description "Extract keys from variable execution times"
     :prerequisites ["intro-cpu-architecture"]
     :tools ["timing-measurement" "network-timing"]
     :discovered_year 1996}

    {:id "cache-timing-attack"
     :name "Cache-Timing Attack Fundamentals"
     :chapter 5
     :complexity "Advanced"
     :risk_level 8
     :description "Infer memory access patterns from cache timing"
     :prerequisites ["cache-l1-l2-l3"]}

    {:id "flush-reload"
     :name "Flush+Reload Cache Attack"
     :chapter 5
     :complexity "Advanced"
     :risk_level 8
     :description "Flush cache lines and measure reload time"
     :prerequisites ["cache-timing-attack"]
     :tools ["clflush" "rdtsc"]
     :discovered_year 2014}

    {:id "prime-probe"
     :name "Prime+Probe Cache Attack"
     :chapter 5
     :complexity "Advanced"
     :risk_level 7
     :description "Prime cache with victim's data, probe eviction patterns"
     :prerequisites ["cache-fundamentals"]
     :discovered_year 2005}

    {:id "evict-time"
     :name "Evict+Time Cache Attack"
     :chapter 5
     :complexity "Advanced"
     :risk_level 7
     :description "Measure access time after evicting victim's cache line"
     :prerequisites ["cache-timing-attack"]}

    {:id "spectre-timing"
     :name "Spectre via Cache Timing"
     :chapter 5
     :complexity "Advanced"
     :risk_level 10
     :description "Use cache-timing to read results of speculative execution"
     :prerequisites ["spectre-v1" "cache-timing-attack"]}

    {:id "constant-time-implementation"
     :name "Constant-Time Implementation (Defense)"
     :chapter 5
     :complexity "Advanced"
     :risk_level 1
     :description "Write cryptographic code to avoid timing leaks"
     :prerequisites ["timing-attack-basic"]}]})

;; ============================================================================
;; CHAPTER 6: ELECTROMAGNETIC & PHYSICAL ATTACKS
;; ============================================================================

(def Chapter6Data
  {:Chapter
   {:id 6
    :title "Electromagnetic, Thermal & Physical Side-Channels"
    :main_concepts ["EM emissions" "Van Eck phreaking" "Acoustic emissions"
                   "Thermal imaging" "Optical emissions" "Physical attacks"]
    :learning_objectives ["Understand EM side-channels"
                         "Learn acoustic cryptanalysis"
                         "Understand thermal imaging attacks"
                         "Learn about physical countermeasures"]}

   :Techniques
   [{:id "electromagnetic-analysis"
     :name "Electromagnetic Analysis (EMA)"
     :chapter 6
     :complexity "Advanced"
     :risk_level 9
     :description "Recover keys from CPU EM emissions"
     :prerequisites ["intro-side-channels"]
     :tools ["RF-probe" "oscilloscope" "antenna"]
     :discovered_year 2002}

    {:id "van-eck-phreaking"
     :name "Van Eck Phreaking (Display Emissions)"
     :chapter 6
     :complexity "Intermediate"
     :risk_level 6
     :description "Recover display contents from EM emissions"
     :prerequisites ["electromagnetic-analysis"]
     :tools ["TV receiver" "antenna"]
     :discovered_year 1985}

    {:id "acoustic-cryptanalysis"
     :name "Acoustic Cryptanalysis"
     :chapter 6
     :complexity "Intermediate"
     :risk_level 7
     :description "Extract keys from CPU acoustic emissions"
     :prerequisites ["intro-side-channels"]
     :tools ["microphone" "FFT analyzer"]
     :discovered_year 2013}

    {:id "acoustic-rsa-key-extraction"
     :name "Acoustic RSA Key Extraction"
     :chapter 6
     :complexity "Advanced"
     :risk_level 8
     :description "Recover full RSA keys from acoustic side-channel"
     :prerequisites ["acoustic-cryptanalysis"]
     :discovered_year 2013}

    {:id "thermal-imaging"
     :name "Thermal Imaging Side-Channel"
     :chapter 6
     :complexity "Intermediate"
     :risk_level 5
     :description "Infer operations from thermal patterns"
     :prerequisites ["intro-side-channels"]
     :tools ["IR camera" "thermal sensor"]}

    {:id "optical-emissions"
     :name "Optical Side-Channels (LED/Display)"
     :chapter 6
     :complexity "Intermediate"
     :risk_level 5
     :description "Leak information from optical emissions"
     :prerequisites ["intro-side-channels"]
     :tools ["photodiode" "camera"]}

    {:id "power-line-coupling"
     :name "Power Line Coupling Attack"
     :chapter 6
     :complexity "Intermediate"
     :risk_level 5
     :description "Measure power via power supply line at distance"
     :prerequisites ["electromagnetic-analysis"]}]})

;; ============================================================================
;; CHAPTER 7: FAULT INJECTION ATTACKS
;; ============================================================================

(def Chapter7Data
  {:Chapter
   {:id 7
    :title "Fault Injection Attacks"
    :main_concepts ["Fault injection" "Glitching" "Laser attacks"
                   "Clock glitching" "Voltage glitching" "Differential fault analysis"]
    :learning_objectives ["Understand fault injection techniques"
                         "Learn exploitation methods"
                         "Understand DFA (Differential Fault Analysis)"
                         "Learn fault injection countermeasures"]}

   :Techniques
   [{:id "fault-injection-overview"
     :name "Fault Injection Attacks (Overview)"
     :chapter 7
     :complexity "Advanced"
     :risk_level 9
     :description "Induce faults to extract cryptographic keys"
     :prerequisites ["intro-side-channels"]
     :tools ["laser" "EM-pulse" "clock-glitch"]}

    {:id "clock-glitching"
     :name "Clock Glitching Attack"
     :chapter 7
     :complexity "Advanced"
     :risk_level 8
     :description "Manipulate clock signal to cause instruction skips"
     :prerequisites ["fault-injection-overview"]
     :tools ["signal-generator"]}

    {:id "voltage-glitching"
     :name "Voltage Glitching Attack"
     :chapter 7
     :complexity "Advanced"
     :risk_level 8
     :description "Manipulate voltage to induce bit flips"
     :prerequisites ["fault-injection-overview"]
     :tools ["power-supply" "glitching-circuit"]}

    {:id "laser-fault-injection"
     :name "Laser Fault Injection"
     :chapter 7
     :complexity "Advanced"
     :risk_level 9
     :description "Use laser pulses to induce faults in silicon"
     :prerequisites ["fault-injection-overview"]
     :tools ["laser" "microscope"]
     :discovered_year 2002}

    {:id "differential-fault-analysis"
     :name "Differential Fault Analysis (DFA)"
     :chapter 7
     :complexity "Advanced"
     :risk_level 9
     :description "Analyze differences between correct/faulty outputs to recover keys"
     :prerequisites ["fault-injection-overview"]
     :discovered_year 1997}

    {:id "electromagnetic-fault-injection"
     :name "Electromagnetic Fault Injection"
     :chapter 7
     :complexity "Advanced"
     :risk_level 8
     :description "Use EM pulses to induce faults without physical contact"
     :prerequisites ["fault-injection-overview"]
     :tools ["EM-pulse-generator"]}]})

;; ============================================================================
;; SIDE-CHANNEL DEFINITIONS
;; ============================================================================

(def SideChannels
  [{:id "power-trace"
    :type "Power"
    :frequency_hz 10
    :measurable_by ["powermetrics" "oscilloscope" "power-analyzer"]
    :signal_strength "Strong"
    :noise_floor -20.0
    :snr_ratio 15.0}

   {:id "thermal-distribution"
    :type "Thermal"
    :frequency_hz 1000
    :measurable_by ["thermal-sensor" "IR-camera" "M5-sensors"]
    :signal_strength "Medium"
    :noise_floor -15.0
    :snr_ratio 10.0}

   {:id "em-emissions"
    :type "EM"
    :frequency_hz 1000000000  ; GHz range
    :measurable_by ["RF-probe" "antenna" "field-probe"]
    :signal_strength "Weak"
    :noise_floor -5.0
    :snr_ratio 5.0}

   {:id "timing-variation"
    :type "Timing"
    :frequency_hz 1000
    :measurable_by ["clock" "performance-counter" "network-timing"]
    :signal_strength "Medium"
    :noise_floor -10.0
    :snr_ratio 8.0}

   {:id "cache-timing"
    :type "Timing"
    :frequency_hz 10000000  ; Cache cycle time
    :measurable_by ["cache-controller" "rdtsc" "perf-counters"]
    :signal_strength "Medium"
    :noise_floor -8.0
    :snr_ratio 7.0}

   {:id "acoustic-emissions"
    :type "Acoustic"
    :frequency_hz 100000  ; Audio + ultrasonic
    :measurable_by ["microphone" "ultrasonic-sensor"]
    :signal_strength "Weak"
    :noise_floor -20.0
    :snr_ratio 5.0}

   {:id "fault-injection"
    :type "Fault"
    :frequency_hz 1000000  ; MHz range
    :measurable_by ["laser" "EM-pulse" "clock-glitch" "voltage-glitch"]
    :signal_strength "Strong"
    :noise_floor 0.0
    :snr_ratio 100.0}

   {:id "optical-emissions"
    :type "Optical"
    :frequency_hz 500000000000  ; THz range
    :measurable_by ["camera" "photodiode" "spectrometer"]
    :signal_strength "Weak"
    :noise_floor -15.0
    :snr_ratio 5.0}])

;; ============================================================================
;; COMPILE ACSet
;; ============================================================================

(def complete-blackhat-acset
  (acset/acset BlackHatGoSchema
    {:Techniques (concat
                   (:Techniques Chapter1Data)
                   (:Techniques Chapter2Data)
                   (:Techniques Chapter3Data)
                   (:Techniques Chapter4Data)
                   (:Techniques Chapter5Data)
                   (:Techniques Chapter6Data)
                   (:Techniques Chapter7Data))
     :SideChannels SideChannels
     :Chapters [(:Chapter Chapter1Data)
                (:Chapter Chapter2Data)
                (:Chapter Chapter3Data)
                (:Chapter Chapter4Data)
                (:Chapter Chapter5Data)
                (:Chapter Chapter6Data)
                (:Chapter Chapter7Data)]}))

;; Export for use in Golang
(defn export-techniques-json []
  (-> complete-blackhat-acset
      :Techniques
      (clojure.data.json/write-str)))

;; Statistics
(defn acset-statistics []
  {:total-techniques (count (:Techniques complete-blackhat-acset))
   :total-side-channels (count (:SideChannels complete-blackhat-acset))
   :total-chapters 7
   :techniques-by-complexity
   (frequencies (map :complexity (:Techniques complete-blackhat-acset)))
   :techniques-by-chapter
   (frequencies (map :chapter (:Techniques complete-blackhat-acset)))
   :average-risk-level
   (double (/ (apply + (map :risk_level (:Techniques complete-blackhat-acset)))
              (count (:Techniques complete-blackhat-acset))))})

(comment
  ;; Print statistics
  (clojure.pprint/pprint (acset-statistics))

  ;; Export for JSON consumption
  (spit "blackhat_go_techniques.json" (export-techniques-json))

  ;; Create ACSet visualization
  (clerk/show complete-blackhat-acset))
