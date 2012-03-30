(ns persistent-data-structures.hash-map
  (:use [persistent-data-structures.utils :only [unsigned-bit-shift-right copy-array]])
  (:import [clojure.lang MapEntry Util]))

(deftype HashMapNode [^objects array])
(defn- hash-map-node? [x] (instance? HashMapNode x))

(def empty-object (Object.))
(defn- empty-object? [x] (identical? empty-object x))

(def width (int 16))
(def bit-width (int 4))
(def bit-mask (int (dec width)))
(def num-levels (int (/ 32 bit-width)))
(defn- empty-node-array [] (to-array (repeat width empty-object)))
(defn- empty-node [] (HashMapNode. (empty-node-array)))

(defn- offset
  [^long i ^long level]
  (bit-and (unsigned-bit-shift-right i (* level bit-width)) bit-mask))

(defn- find-object
  [^HashMapNode root i object]
  (loop [^HashMapNode r root i i obj object level num-levels ret []]
    (if (= 0 level)
      (if (empty-object? r)
        (cons empty-object (conj ret (offset i 0)))
        (let [^objects arr (.array r)
              o2 (aget arr (offset i 0))]
          (cons (if (empty-object? o2) o2 (val o2)) (conj ret (offset i 0)))))
      (if (empty-object? r)
        (recur r i obj (dec level) (conj ret (offset i level)))
        (let [^objects arr (.array r)
              new-r (aget arr (offset i level))]
          (recur new-r i obj (dec level) (conj ret (offset i level))))))))

(defn- only-find-object
  [^HashMapNode root i object]
  (loop [^HashMapNode r root level num-levels]
    (if (empty-object? r)
      r
      (let [^objects arr (.array r)
            o2 (aget arr (offset i level))]
        (if (= 0 level)
          (if (empty-object? o2) o2 (val o2))
          (recur o2 (dec level)))))))

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
    (let [poss-val (first (find-object root (hash key) key))]
     (when (not (empty-object? poss-val))
       (MapEntry. key poss-val))))

  (assoc [this key val]
    (let [places (rest (find-object root (hash key) key))
          helper (fn helper [p ^HashMapNode r]
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
                       (mapcat (fn [^HashMapNode x] (helper (.array x))) children)
                       children)))]
      (helper (.array root))))

  (count [this] cnt)

  (without [this key]
    ;; TODO
    )

  clojure.lang.ILookup
  (valAt [this key not-found]
    (let [poss-val (only-find-object root (hash key) key)]
      (if (empty-object? poss-val)
        not-found
        poss-val)))
  (valAt [this key]
    (let [ans (only-find-object root (hash key) key)]
      (when-not (empty-object? ans)
        ans)))


  )

(defn empty-phash-map []
  (PHashMap. 0 (empty-node) {}))

(comment
  (def p (empty-phash-map))

  p
  (find-object (.root (assoc p 1 2)) 3 3)
  (assoc (assoc p 1 2) 2 3)
  (apply assoc p (range 200))
  (.containsKey (assoc p 1 2) 1)
  (let [q (apply assoc (empty-phash-map) (range 800))]
   (time (dotimes [n 100]
           (get q (rand-int 800)))))
  
  (let [q (apply assoc {} (range 800))]
    (time (dotimes [n 100]
            (get q (rand-int 800)))))
  (time (dotimes [n 100]
          (apply assoc (empty-phash-map) (range 200))))
  (time (dotimes [n 100]
          (apply assoc {} (range 200))))
  (seq (assoc p 1 2))
  (get (assoc p 1 2) 2 empty-object)
  (.containsKey p 2)
  (identical? empty-object (find-object (empty-node) (find-object-place (empty-node) 1 1)))
  (rand-int (* 32 32))
  (set! *warn-on-reflection* true)
  )
