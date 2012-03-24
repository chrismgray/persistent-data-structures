(ns persistent-data-structures.vector
  (:import clojure.lang.MapEntry))

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

(deftype ArrChunk [^objects array off end _meta]
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

(deftype ChunkedVector [vec ^objects node i offset _meta]
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

;; We begin by defining some helper functions and a protocol for some
;; private methods of PersistentVector that are needed for the
;; implementation.

;; Most of the functions defined in this protocol could be moved into
;; `let`s inside the implementations that they are helping.  However,
;; `arrayFor` is used by the chunked sequence to get the next chunk,
;; so it can not.  However, it should be possible to define it using
;; `defn` if that will make things faster or easier to understand.

(defprotocol IPVector
  "Vector functions that are not part of an existing protocol or interface."
  (tailoff [this])
  (arrayFor [this i])
  (new-path [this level node])
  (push-tail [this level parent tail-node]))

(defn- unsigned-bit-shift-right
  "Shifts the input `x` to the right by `n` places and sets the leftmost bit to 0."
  [^long x ^long n]
  (bit-and 0xefffffff (bit-shift-right x n)))

(defn- copy-array
  "Copy the elements in `from-array` to `to-array`.  Assumes that
   `to-array` is as long as `from-array`."
  [^objects from-array ^objects to-array]
  (loop [c (count from-array)]
    (when (> c 0)
      (aset to-array (dec c) (aget from-array (dec c)))
      (recur (dec c))))
  to-array)

;; ### The persistent vector type.

;; As a data structure, it's pretty simple.  There is a tree structure
;; with a fan-out of 32 that is created by linking `VectorNode`s to
;; one another, and there is a `tail`, which is simply an array of
;; less than 32 elements that when full will be added to the tree
;; structure.

;; One benefit of having the fan-out be 32 (or any power of two
;; really) is that the `k`th element can be found easily using
;; bit-twiddling operations.  For the sake of example and to keep the
;; numbers small, let's imagine that the fan-out was 4, and that there
;; were 65 elements in the vector.  Then we would have the situation
;; where there is a tail with one element in it and a full tree that
;; is three levels high.  Let's try to find the 27th element.  The
;; number 27 is 011011 in binary.  We can figure out which sub-tree of
;; the root that the element is in by looking at sub-tree number
;; (010111 >> (2 * 2)) & 11 = 01 (where the numbers with only 1s and
;; 0s are in binary, >> denotes right-shift, and & denotes
;; bitwise-and).  We find the subtree of that tree containing the 27th
;; element by looking at sub-tree number (010111 >> (1 * 2)) & 11 =
;; 10, and finally we look at element number (010111 >> (0 * 2)) & 11
;; = 11 to find the element itself.

(deftype PVector [^int cnt ^int shift ^VectorNode root ^objects tail _meta]
  clojure.lang.IObj
  (meta [this] _meta)
  (withMeta [this m]
    (PVector. cnt shift root tail m))
  
  clojure.lang.IPersistentVector
  (length [this] cnt)

  ;; Change the `i`th value in the vector to `val`.
  
  (assocN [this i val]
    (cond (and (>= i 0) (< i cnt))
          (if (>= i (.tailoff this))
            (let [^objects new-tail (to-array (repeat (count tail) (Object.)))
                  _ (copy-array tail new-tail)
                  _ (aset new-tail (bit-and i 0x1f) val)]
              (PVector. cnt shift root new-tail _meta))
            (let [do-assoc (fn do-assoc [level node i val]
                             (let [node-array (.array node)
                                   new-array (to-array (repeat (count node-array) (Object.)))
                                   _ (copy-array node-array new-array)
                                   new-node (VectorNode. new-array)]
                               (if (= level 0)
                                 (do (aset new-array (bit-and i 0x01f) val)
                                     new-node)
                                 (let [subidx (bit-and (unsigned-bit-shift-right i level) 0x01f)]
                                   (aset new-array subidx (do-assoc (- level 5) (aget node-array subidx) i val))
                                   new-node))))]
              (PVector. cnt shift (do-assoc shift root i val) tail _meta)))
          (= i cnt)
          (.cons this val)
          :else
          (throw (IndexOutOfBoundsException.))))

  ;; Add an element to the end of the vector.
  
  (cons [this o]
    (if (< (- cnt (.tailoff this)) 32)
      (let [tail-count (count tail)
            ^objects new-tail (to-array (repeat (inc tail-count) (Object.)))
            _ (copy-array tail new-tail)
            _ (aset new-tail tail-count o)]
        (PVector. (inc cnt) shift root new-tail _meta))
      (let [tail-node (VectorNode. tail)
            overflow-root? (> (unsigned-bit-shift-right cnt 5) (bit-shift-left 1 shift))
            [new-shift new-root]
            (if overflow-root?
              (let [^objects new-root-array (to-array (repeat 32 (Object.)))
                    _ (aset new-root-array 0 root)
                    _ (aset new-root-array 1 (.new-path this shift tail-node))]
                [(+ shift 5) (VectorNode. new-root-array)])
              [shift (.push-tail this shift root tail-node)])]
        (PVector. (inc cnt) new-shift new-root (to-array (list o)) _meta))))
  
  clojure.lang.IPersistentCollection
  (empty [this]
    (PVector. 0 5 empty-node (to-array '()) _meta))

  ;; Check whether another sequence has all the same elements as this
  ;; vector.
  
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

  clojure.lang.Associative

  (assoc [this key val]
    (if (integer? key)
      (.assocN this key val)
      (throw (IllegalArgumentException. "Key must be integer"))))

  (entryAt [this key]
    (when (.containsKey this key)
      (MapEntry. key (.nth this key))))

  (containsKey [this key]
    (and (integer? key) (>= key 0) (< key cnt)))
  
  IPVector

  ;; The `i` for which elements larger than `i` are put in the tail.
  
  (tailoff [this]
    (if (< cnt 32)
      0
      (bit-shift-left (unsigned-bit-shift-right (dec cnt) 5) 5)))

  ;; Find the node containing the `i`th element
  
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
      (let [^objects new-array (to-array (repeat 32 (Object.)))
            ret (VectorNode. new-array)
            _ (aset new-array 0 (.new-path this (- level 5) node))]
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

  ;; Return the last element of the vector
  
  (peek [this]
    (if (> (.count this) 0)
      (.nth this (dec cnt))))

  ;; Return the vector without its last element.
  ;; Not yet implemented.

  (pop [this]
    (throw (UnsupportedOperationException.)))
  
  clojure.lang.Seqable
  (seq [this]
    (ChunkedVector. this (.arrayFor this 0) 0 0 {}))
  
  clojure.lang.Reversible
  (rseq [this]
    (throw (UnsupportedOperationException.)))
  
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

;; ### Creating the persistent vector

;; The naive way of constructing a persistent vector from a collection
;; is to repeatedly `conj` elements of the collection onto the empty
;; vector.  Though this works, it is slow for a couple of reasons.
;; First, it creates a lot of extra objects to be GC'd without a lot
;; of purpose.  Second, it takes O(n log n) time (where the base of
;; the log is 32, so the log n factor will always be pretty small, but
;; still) rather than the O(n) time that is both optimal and possible.

;; The algorithm works from the bottom up by repeatedly partitioning
;; the input into groups of 32.  Since the size of the input at each
;; step is a constant fraction of the previous size, and a linear
;; amount of work is done at each step, this is a linear-time
;; algorithm.

(defn pvec
  "Construct a PVector from the collection `coll` in linear time."
  [coll]
  (let [grouped-coll (partition 32 32 (list) coll)
        big-groups (butlast grouped-coll)
        tail (to-array (last grouped-coll))
        c (count coll)
        shift (loop [level 0 c (unsigned-bit-shift-right c 5)]
                 (if (<= c 32)
                   (* 5 (inc level))
                   (recur (inc level) (bit-shift-right c 5))))
        root (loop [groups big-groups]
               (let [vector-nodes (map #(VectorNode. (to-array %)) groups)]
                 (if (<= (count groups) 32)
                   (VectorNode. (to-array (first (partition 32 vector-nodes))))
                   (recur (partition 32 32 (list) vector-nodes)))))]
    (PVector. c shift root tail {})))

(defn empty-pvector
  "Create an empty PVector"
  []
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