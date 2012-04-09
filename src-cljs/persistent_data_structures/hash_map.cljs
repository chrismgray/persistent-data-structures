(ns persistent-data-structures.hash-map)

(deftype HashMapNode [prefix mask zero-branch one-branch kvs]
  ;; Dummy seq implementation for debugging purposes
  clojure.lang.Seqable
  (seq [this]
    (list prefix mask kvs (seq zero-branch) (seq one-branch))))
(defn- hash-map-node? [x] (instance? HashMapNode x))

;; Create an empty object to test against
(def ^:private empty-object (js-obj))
(defn- empty-object? [x] (identical? empty-object x))

(defn root-node [] (HashMapNode. 0 0 nil nil nil))

(defn- find-object
  "Return the key-value pair where `object` is the key with hash
   `hash` if it exists in the radix-tree rooted at `root`.  Otherwise,
   return `not-found`."
  [^HashMapNode root hash object not-found]
  (if (nil? root)
    not-found
   (let [pref (.-prefix root)
         mask (.-mask root)
         kvs (.-kvs root)
         zero-branch (.-zero-branch root)
         one-branch (.-one-branch root)]
     (if kvs
       (or (some #(when (= object (first %)) %) kvs) not-found)
       (if (zero? mask)
         (if (< hash (bit-shift-left 1 31))
           (recur zero-branch hash object not-found)
           (recur one-branch hash object not-found))
         (if (zero? (bit-xor (bit-and hash mask) pref))
           (if (zero? (bit-and (bit-not mask) (bit-and (bit-shift-right mask 1) hash)))
             (recur zero-branch hash object not-found)
             (recur one-branch hash object not-found))
           not-found))))))

(defn- insert-object
  "Insert the key-value pair `kv` into the radix-tree rooted at
   `root`.  The object that is the key must have hash `hash`."
  [^HashMapNode root hash kv]
  (if (nil? root)
    (HashMapNode. hash 0xffffffff nil nil (list kv))
    (let [pref (.-prefix root)
          mask (.-mask root)
          kvs (.-kvs root)
          zero-branch (.-zero-branch root)
          one-branch (.-one-branch root)]
      (if (zero? mask)
          (if (< hash (bit-shift-left 1 31))
            (HashMapNode. pref mask (insert-object zero-branch hash kv) one-branch kvs)
            (HashMapNode. pref mask zero-branch (insert-object one-branch hash kv) kvs))
          (if (zero? (bit-xor (bit-and hash mask) pref))
            ;; Prefixes are the same, see if we're at a leaf
            (if kvs
              (HashMapNode. pref mask zero-branch one-branch (cons kv (remove #(= (first kv) (key %)) kvs)))
              (if (zero? (bit-and (bit-not mask) (bit-and (bit-shift-right mask 1) hash)))
                (HashMapNode. pref mask (insert-object zero-branch hash kv) one-branch kvs)
                (HashMapNode. pref mask zero-branch (insert-object one-branch hash kv) kvs)))
            ;; Insert the node between root and the previous node
            (let [[new-pref new-mask]
                  (loop [new-mask (bit-shift-left mask 1)]
                    (if (= 0 (bit-xor (bit-and hash new-mask) (bit-and pref new-mask)))
                      [(bit-and pref new-mask) new-mask]
                      (recur (bit-shift-left new-mask 1))))]
              (if (zero? (bit-and (bit-not new-mask) (bit-and (bit-shift-right new-mask 1) pref)))
                (HashMapNode. new-pref new-mask root (insert-object nil hash kv) nil)
                (HashMapNode. new-pref new-mask (insert-object nil hash kv) root nil))))))))

(declare empty-phash-map)

(deftype PHashMap [cnt ^HashMapNode root _meta]
  IMeta
  (-meta [this] _meta)
  IWithMeta
  (-with-meta [this m]
    (PHashMap. cnt root m))

  IAssociative
  (-contains-key? [this key]
    (let [ans (find-object root (hash key) key empty-object)]
     (not (or (empty-object? ans) (empty-object? (second ans))))))

  (-assoc [this key val]
    (let [h (hash key)
          ans (find-object root h key empty-object)
          cont (or (empty-object? ans) (empty-object? (second ans)))]
     (PHashMap. (if cont cnt (inc cnt)) (insert-object root h [key val]) _meta)))

  IEmptyableCollection
  (-empty [this] (empty-phash-map))

  ICollection
  (-conj [this kv & more]
    (let [[item value] kv]
     (if more
       (reduce -conj (-assoc this item value) more)
       (-assoc this item value))))

  IEquiv
  (-equiv [this other] (equiv-map this other))

  IHash
  (-hash [coll] (hash-coll coll))

  ISeqable
  (-seq [this]
    (let [helper
          (fn helper [^HashMapNode root]
            (if (nil? root)
              nil
             (let [kvs (-.kvs root)]
               (if kvs
                 (remove (comp empty-object? second) kvs)
                 (concat (helper (-.zero-branch root)) (helper (-.one-branch root)))))))]
      (helper root)))

  ICounted
  (count [this] cnt)

  (without [this key]
    (-assoc this key empty-object))

  ILookup
  (-lookup [this key not-found]
    (let [poss-val (find-object root (hash key) key empty-object)]
      (if (or (empty-object? poss-val) (empty-object? (second poss-val)))
        not-found
        (second poss-val))))
  (-lookup [this key]
    (-lookup this key nil)))

(defn empty-phash-map []
  (PHashMap. 0 (root-node) {}))

(dotimes [n 1000]
  (apply assoc (empty-phash-map) (range 1000)))

;; (let [q (apply assoc (empty-phash-map) (range 1000))]
;;   (dotimes [n 100000]
;;     (get q 998)))

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
  (rand-int (* 32 32))
  (set! *warn-on-reflection* true)
  )
