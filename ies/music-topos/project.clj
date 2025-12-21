(defproject music-topos "0.1.0"
  :description "Music Topos: Category Theory in Sound (pure OSC)"
  :url "https://github.com/bob/music-topos"
  :license {:name "MIT"}
  :dependencies [[org.clojure/clojure "1.11.1"]
                 [org.clojure/core.async "1.6.681"]
                 [overtone/osc-clj "0.9.0"]
                 [metosin/jsonista "0.3.8"]]
  :jvm-opts ["-Duser.timezone=UTC"
             "-Xmx2g"]
  :main music-topos.core)
