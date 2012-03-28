(defproject persistent-data-structures "1.0.0-SNAPSHOT"
  :description "FIXME: write description"
  :dependencies [[org.clojure/clojure "1.4.0-alpha2"]]
  :cljsbuild {
              :source-path "src-cljs"
              :compiler {
                         :output-to "foo"
                         :optimizations :whitespace
                         :pretty-print true
                         }
              }
  :dev-dependencies [[lein-marginalia "0.7.0"]])