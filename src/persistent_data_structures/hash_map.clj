(ns persistent-data-structures.hash-map
  (:use [persistent-data-structures.utils :only [unsigned-bit-shift-right copy-array]])
  (:import [clojure.lang MapEntry Util]))

(deftype HashMapNode [^objects array])
(defn- hash-map-node? [x] (instance? HashMapNode x))

(def empty-object (Object.))
(defn- empty-object? [x] (identical? empty-object x))

(defn- empty-node-array [] (to-array (repeat 16 empty-object)))
(defn- empty-node [] (HashMapNode. (empty-node-array)))

(defn- offset
  [i level]
  (bit-and (unsigned-bit-shift-right i (bit-shift-left level 2)) 0xf))

(defn- cyclic-range-for
  [i level]
  (let [off (offset i level)]
    (take 16 (drop off (cycle (range 16))))))

(defn- find-object
  "Find the place with the object with hash `i` in the tree rooted at `root`."
  [^HashMapNode root i object]
  (first
   (let [get-from (fn [r num]
                    (if (empty-object? r)
                      r
                      (let [^objects arr (.array r)]
                        (aget arr num))))]
    (for [a (cyclic-range-for i 7)
          b (cyclic-range-for i 6)
          c (cyclic-range-for i 5)
          d (cyclic-range-for i 4)
          e (cyclic-range-for i 3)
          f (cyclic-range-for i 2)
          g (cyclic-range-for i 1)
          h (cyclic-range-for i 0)
          :let [obj (reduce get-from root [a b c d e f g h])]
          :when (or (empty-object? obj)
                    (= object (key obj)))]
      [obj a b c d e f g h]))))

(declare empty-phash-map)

(deftype PHashMap [cnt ^HashMapNode root _meta]
  clojure.lang.IObj
  (meta [this] _meta)
  (withMeta [this m]
    (PHashMap. cnt root m))

  clojure.lang.IPersistentMap
  (containsKey [this key]
    (not (empty-object? (first (find-object root (hash key) key)))))
  (entryAt [this key]
    (when (.containsKey this key)
      (MapEntry. key (first (find-object root (hash key) key)))))

  (assoc [this key val]
    (let [places (rest (find-object root (hash key) key))
          helper (fn helper [p r]
                   (if (empty? p)
                     (MapEntry. key val)
                     (let [^objects this-arr (when-not (empty-object? r)
                                               (.array r))
                           ^objects new-arr (empty-node-array)]
                       (when-not (empty-object? r)
                         (copy-array this-arr new-arr))
                       (aset new-arr (first p) (helper (rest p) (aget new-arr (first p))))
                       (HashMapNode. new-arr))))]
      (PHashMap. (if (.containsKey this key) cnt (inc cnt)) (helper places root) _meta)))

  (empty [this] (empty-phash-map))
  (cons [this [item value]] (.assoc this item value))
  (seq [this]
    (let [helper (fn helper [^objects r]
                   (let [children (remove empty-object? r)]
                     (if (and (seq children) (hash-map-node? (first children)))
                       (mapcat #(helper (.array %)) children)
                       children)))]
      (helper (.array root))))

  (count [this] cnt)

  (without [this key]
    ;; TODO
    )

  clojure.lang.ILookup
  (valAt [this key not-found]
    (if (.containsKey this key)
      (val (.entryAt this key))
      not-found))
  (valAt [this key]
    (let [ans (.valAt this key empty-object)]
      (when-not (empty-object? ans)
        ans)))


  )

(defn empty-phash-map []
  (PHashMap. 0 (empty-node) {}))

(comment
  (def p (empty-phash-map))

  p
  (.containsKey (assoc p 1 2) 1)
  (let [q (apply assoc p (range 200))]
   (time (dotimes [n 100]
           (get q (rand-int 200)))))
  
  (let [q (apply assoc {} (range 200))]
    (time (dotimes [n 100]
            (get q (rand-int 200)))))
  (seq (assoc p 1 2))
  (get (assoc p 1 2) 2 empty-object)
  (.containsKey p 2)
  (identical? empty-object (find-object (empty-node) (find-object-place (empty-node) 1 1)))
  (rand-int (* 32 32))
  (set! *warn-on-reflection* true)
  )
