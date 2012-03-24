(ns persistent-data-structures.vector)

;; # Persistent Vector

;; This is an implementation of Clojure's persistent vector data
;; structure in pure Clojure, using only arrays.  It aims to be a
;; faithful porting of Rich's initial implementation from Java to
;; Clojure.

;; ## Why?

;; As Clojure gets ported to new backends such as Javascript and
;; Scheme, the persistent data structures that make Clojure such a joy
;; to use are generally not ported.  Thus, some assumptions about
;; running times become invalid.  It is generally easier to port the
;; array operations to a new backend, since nearly all languages have
;; arrays built in.

;; # The Implementation

;; ## The Node

;; A node is just an array of 32 objects.  They either point to other
;; nodes or contain the objects that are in the vector.

(deftype VectorNode [array])

(def empty-node (VectorNode. (to-array (take 32 (repeat (Object.))))))

;; ## Chunked Sequences

(deftype ArrChunk [array off end _meta]
  clojure.lang.IObj
  (meta [this] _meta)
  (withMeta [this m] (ArrChunk. array off end m))
  clojure.lang.IChunk
  (nth [this i]
    (aget array (+ off i)))
  (nth [this i not-found]
    (if (and (>= i 0) (< i (.count this)))
      (.nth this i)
      not-found))
  (count [this]
    (- end off))
  (dropFirst [this]
    (if (= off end)
      (throw (IllegalStateException. "dropFirst of empty chunk"))
      (ArrChunk. array (inc off) end {})))
  (reduce [this f start]
    (reduce f start (drop off array))))

(deftype ChunkedVector [vec node i offset _meta]
  clojure.lang.IChunkedSeq
  (chunkedFirst [this] (ArrChunk. node offset (count node) {}))
  (chunkedNext [this]
    (when (< (+ i (count node)) (.count vec))
      (ChunkedVector. vec (.arrayFor vec (+ i (count node))) (+ i (count node)) 0 _meta)))
  (chunkedMore [this]
    (if-let [s (.chunkedNext this)]
      s
      (list)))
  (first [this]
    (aget node offset))
  (next [this]
    (if (< (inc offset) (count node))
      (ChunkedVector. vec node i (inc offset) _meta)
      (.chunkedNext this)))
  clojure.lang.Seqable
  (seq [this] this)
  clojure.lang.IObj
  (meta [this] _meta)
  (withMeta [this m]
    (ChunkedVector. vec node i offset m)))

;; ## The Vector

(defprotocol IPVector
  "Vector functions that are not part of an existing protocol or interface."
  (tailoff [this])
  (arrayFor [this i])
  (new-path [this level node])
  (push-tail [this level parent tail-node]))

(defn- unsigned-bit-shift-right
  "Shifts the input `x` to the right by `n` places and sets the leftmost bit to 0."
  [x n]
  (bit-and 0xefffffff (bit-shift-right x n)))

(defn- copy-array
  "Copy the elements in `from-array` to `to-array`.  Assumes that
   `to-array` is as long as `from-array`."
  [from-array to-array]
  (loop [c (count from-array)]
    (when (> c 0)
      (aset to-array (dec c) (aget from-array (dec c)))
      (recur (dec c))))
  to-array)

(deftype PVector [^int cnt ^int shift ^VectorNode root ^objects tail _meta]
  clojure.lang.IObj
  (meta [this] _meta)
  (withMeta [this m]
    (PVector. cnt shift root tail m))
  clojure.lang.IPersistentVector
  (length [this] cnt)
  (assocN [this i val]
    (cond (and (>= i 0) (< i cnt))
          (if (>= i (.tailoff this))
            (let [new-tail (to-array (repeat (count tail) (Object.)))
                  _ (copy-array tail new-tail)
                  _ (aset new-tail (bit-and i 0x1f) val)]
              (PVector. cnt shift root new-tail _meta))
            (let [do-assoc (fn do-assoc [level node i val]
                             (let [new-array (to-array (repeat (count (.array node)) (Object.)))
                                   _ (copy-array (.array node) new-array)
                                   new-node (VectorNode. new-array)]
                               (if (= level 0)
                                 (do (aset new-array (bit-and i 0x01f) val)
                                     new-node)
                                 (let [subidx (bit-and (unsigned-bit-shift-right i level) 0x01f)]
                                   (aset new-array subidx (do-assoc (- level 5) (aget (.array node)) i val))
                                   new-node))))]
              (PVector. cnt shift (do-assoc shift root i val) tail _meta)))
          (= i cnt)
          (.cons this val)
          :else
          (throw (IndexOutOfBoundsException.))))
  (cons [this o]
    (if (< (- cnt (.tailoff this)) 32)
      (let [new-tail (to-array (repeat (inc (count tail)) (Object.)))
            _ (copy-array tail new-tail)
            _ (aset new-tail (count tail) o)]
        (PVector. (inc cnt) shift root new-tail _meta))
      (let [tail-node (VectorNode. tail)
            overflow-root? (> (unsigned-bit-shift-right cnt 5) (bit-shift-left 1 shift))
            [new-shift new-root]
            (if overflow-root?
              (let [new-root-array (to-array (repeat 32 (Object.)))
                    _ (aset new-root-array 0 root)
                    _ (aset new-root-array 1 (.new-path this shift tail-node))]
                [(+ shift 5) (VectorNode. new-root-array)])
              [shift (.push-tail this shift root tail-node)])]
        (PVector. (inc cnt) new-shift new-root (to-array (list o)) _meta))))
  clojure.lang.IPersistentCollection
  (empty [this]
    (PVector. 0 5 empty-node (to-array '()) _meta))
  (equiv [this o]
    (if (or (list? o) (vector? o))
      (if (not= (count o) (.count this))
        false
        (every? (map = o (.seq this))))
      (if (not (sequential? o))
        false
        (loop [s (.seq this) a (seq o)]
          (cond (and (nil? s) (nil? a))
                true
                (nil? s)
                false
                (nil? a)
                false
                (not= (first s) (first a))
                false
                :else
                (recur (rest s) (rest a)))))))
  IPVector
  (tailoff [this]
    (if (< cnt 32)
      0
      (bit-shift-left (unsigned-bit-shift-right (dec cnt) 5) 5)))
  (arrayFor [this i]
    (if (and (>= i 0) (< i cnt))
      (if (>= i (.tailoff this))
        tail
        (loop [^VectorNode node root level shift]
          (let [^objects arr (.array node)]
           (if (<= level 0)
             arr
             (let [new-node (aget arr (bit-and (unsigned-bit-shift-right i level) 0x01f))]
               (recur new-node (- level 5)))))))
      (throw (IndexOutOfBoundsException.))))
  (new-path [this level node]
    (if (= level 0)
      node
      (let [ret (VectorNode. (to-array (repeat 32 (Object.))))
            _ (aset (.array ret) 0 (.new-path this (- level 5) node))]
        ret)))
  (push-tail [this level parent tail-node]
    (let [subidx (bit-and (unsigned-bit-shift-right (dec cnt) level) 0x01f)
          ^objects parent-array (.array parent)
          ^objects new-arr (to-array (repeat (count parent-array) (Object.)))
          _ (copy-array parent-array new-arr)
          ret (VectorNode. new-arr)
          node-to-insert (if (= level 5)
                           tail-node
                           (let [child (aget parent-array subidx)]
                             (if child
                               (push-tail this (- level 5) child tail-node)
                               (new-path this (- level 5) tail-node))))
          _ (aset new-arr subidx node-to-insert)]
      ret))
  clojure.lang.IPersistentStack
  (peek [this]
    (if (> (.count this) 0)
      (.nth this (dec cnt))))
  (pop [this]
    ;; TODO
    )
  clojure.lang.Seqable
  (seq [this]
    (ChunkedVector. this (.arrayFor this 0) 0 0 {}))
  clojure.lang.Reversible
  (rseq [this]
    ;; TODO
    )
  clojure.lang.IFn
  (invoke [this k] (.nth this k))
  (invoke [this k not-found] (.nth this k not-found))
  clojure.lang.Indexed
  (nth [this ^int i]
    (let [^objects node (.arrayFor this i)]
      (aget node (bit-and i 0x01f))))
  (nth [this i not-found]
    (if (and (>= i 0) (< i cnt))
      not-found
      (.nth this i)))
  clojure.lang.Counted
  (count [this]
    cnt))

(defn empty-pvector []
  (PVector. 0 5 empty-node (to-array '()) {}))


(comment
  (def m (empty-pvector))
  (sequential? m)
  (def o (-> m (conj 1) (conj 2)))
  (def p (reduce conj m (range 120)))
  (time
   (dotimes [n 100]
    (nth p 64)))
  (def q (vec (range 120)))
  (time
   (dotimes [n 100]
     (nth q 64)))
  )