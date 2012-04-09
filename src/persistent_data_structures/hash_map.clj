(ns persistent-data-structures.hash-map
  (:use [persistent-data-structures.utils :only [unsigned-bit-shift-right copy-array]])
  (:import [clojure.lang MapEntry Util]))

(deftype HashMapNode [^long prefix ^long mask zero-branch one-branch kvs]
  clojure.lang.Seqable
  (seq [this]
    (list prefix mask kvs (seq zero-branch) (seq one-branch))))
(defn- hash-map-node? [x] (instance? HashMapNode x))

(def empty-object (Object.))
(defn- empty-object? [x] (identical? empty-object x))

(defn root-node [] (HashMapNode. 0 0 nil nil nil))

(defn- find-object [^HashMapNode root hash object not-found]
  (if (nil? root)
    not-found
   (let [pref (.prefix root)
         mask (.mask root)
         kvs (.kvs root)
         zero-branch (.zero-branch root)
         one-branch (.one-branch root)]
     (if kvs
       (or (some #(when (= object (key %)) %) kvs) not-found)
       (if (zero? mask)
         (if (< hash (bit-shift-left 1 31))
           (recur zero-branch hash object not-found)
           (recur one-branch hash object not-found))
         (if (zero? (bit-xor (bit-and hash mask) pref))
           ;; Now we know that the prefixes are the same
           ;; We just need to figure out which tree to descend into
           (if (zero? (bit-and (bit-not mask) (bit-and (bit-shift-right mask 1) hash)))
             (recur zero-branch hash object not-found)
             (recur one-branch hash object not-found))
           not-found))))))

(defn- insert-object [^HashMapNode root hash [k v :as kv]]
  (if (nil? root)
    (HashMapNode. hash 0xffffffff nil nil (list (MapEntry. k v)))
    (let [pref (.prefix root)
          mask (.mask root)
          kvs (.kvs root)
          zero-branch (.zero-branch root)
          one-branch (.one-branch root)]
      (if (zero? mask)
          (if (< hash (bit-shift-left 1 31))
            (HashMapNode. pref mask (insert-object zero-branch hash kv) one-branch kvs)
            (HashMapNode. pref mask zero-branch (insert-object one-branch hash kv) kvs))
          (if (not= 0 (bit-xor (bit-and hash mask) pref))
            ;; Insert the node between root and the previous node
            (let [[new-pref new-mask]
                  (loop [new-mask (bit-shift-left mask 1)]
                    (if (= 0 (bit-xor (bit-and hash new-mask) (bit-and pref new-mask)))
                      [(bit-and pref new-mask) new-mask]
                      (recur (bit-shift-left new-mask 1))))]
              (if (zero? (bit-and (bit-not new-mask) (bit-and (bit-shift-right new-mask 1) pref)))
                (HashMapNode. new-pref new-mask root (insert-object nil hash kv) nil)
                (HashMapNode. new-pref new-mask (insert-object nil hash kv) root nil)))
            ;; Prefixes are the same, see if we're at a leaf
            (if kvs
              (HashMapNode. pref mask zero-branch one-branch (cons (MapEntry. k v) (remove #(= k (key %)) kvs)))
              (if (zero? (bit-and (bit-not mask) (bit-and (bit-shift-right mask 1) hash)))
                (HashMapNode. pref mask (insert-object zero-branch hash kv) one-branch kvs)
                (HashMapNode. pref mask zero-branch (insert-object one-branch hash kv) kvs))))))))

(declare empty-phash-map)

(deftype PHashMap [cnt ^HashMapNode root _meta]
  clojure.lang.IObj
  (meta [this] _meta)
  (withMeta [this m]
    (PHashMap. cnt root m))

  clojure.lang.IPersistentMap
  (containsKey [this key]
    (not (empty-object? (find-object root (hash key) key empty-object))))
  (entryAt [this key]
    (let [poss-val (find-object root (hash key) key empty-object)]
      (when-not (empty-object? poss-val)
        (MapEntry. key (second poss-val)))))

  (assoc [this key val]
    (PHashMap. (if (.containsKey this key) cnt (inc cnt)) (insert-object root (hash key) [key val]) _meta))

  (empty [this] (empty-phash-map))
  (cons [this [item value]] (.assoc this item value))
  (seq [this]
    (let [helper
          (fn helper [^HashMapNode root]
            (if (nil? root)
              nil
             (let [kvs (.kvs root)]
               (if kvs
                 (remove (comp empty-object? val) kvs)
                 (concat (helper (.zero-branch root)) (helper (.one-branch root)))))))]
      (helper root)))

  (count [this] cnt)

  (without [this key]
    (.assoc this key empty-object))

  clojure.lang.ILookup
  (valAt [this key not-found]
    (let [poss-val (find-object root (hash key) key empty-object)]
      (if (or (empty-object? poss-val) (empty-object? (val poss-val)))
        not-found
        (val poss-val))))
  (valAt [this key]
    (let [ans (find-object root (hash key) key empty-object)]
      (when-not (or (empty-object? ans) (empty-object? (val ans)))
        (val ans)))))

(defn empty-phash-map []
  (PHashMap. 0 (root-node) {}))

(comment
  (def p (empty-phash-map))

  (seq (.root (assoc p 1 2)))
  p
  (find-object (.root (assoc p 1 2)) 3 3)
  (seq (.root (assoc (assoc p 1 2) 2 3)))
  (seq (.root (apply assoc p (range 10))))
  (.containsKey (assoc p 1 2) 1)
  (get (assoc p 1 2) 1)
  (let [q (apply assoc (empty-phash-map) (range 1600))]
   (time (dotimes [n 10000]
           (get q (rand-int 800)))))

  (get (dissoc (assoc (empty-phash-map) 1 3 2 4 2 5) 2) 2)

  (time (dotimes [n 100]
          (apply assoc (empty-phash-map) (range 10000))))
  (time (dotimes [n 100]
          (apply assoc {} (range 10000))))

  (let [q (apply assoc {} (range 1600))]
    (time (dotimes [n 10000]
            (get q (rand-int 800)))))
  (time (dotimes [n 100]
          (apply assoc (empty-phash-map) (range 200))))
  (time (dotimes [n 100]
          (apply assoc {} (range 200))))
  (seq (assoc p 1 2))
  (get (assoc p 1 2) 2 empty-object)
  (.containsKey p 2)
  (identical? empty-object (find-object (empty-node) (find-object-place (empty-node) 1 1)))

  (hash -3)
  (rand-int (* 32 32))
  (set! *warn-on-reflection* true)
  )
