(ns contract.typed
  "A typed contracts system.
  
  (contract int-c 1)
  ;=> 1

  (contract int-c nil)
  ; Blame positive"
  {:lang :core.typed}
  (:require [clojure.core.typed :as t]))

;; (contract int-c 1)
;; ;=> 1
;;
;; (contract int-c 1)
;; ;Error! Blame provider of 1
;;
;; make-contract
;; - :first-order
;; - :projection 
;; make-blame

(t/defalias StrSym
  "A string or a symbol"
  (t/U t/Str t/Sym))

(t/defalias Blame
  "A blame object contains both positive and negative blame.
  
  The positive blame party is the *sender* of the data. They
  have responsibility in providing values of the expected shape 
  and behaviour.

  The negative blame party is the *receiver* of the data. Their
  responsibility is to correctly *use* incoming values that respect
  their contract.

  Say you require me (Ambrose) to provide you something that satisfies the
  integer contract.

  You write 
    (contract Int (ambrose)), 
  and now I have a chance to provide a value that satisfies your contract.

  In this transaction:
    - positive blame = Ambrose
    - negative blame = You

  If the contract fails, the positive blame party is blamed (Ambrose), since
  I failed to provide you with the correct shape of data.
  
  The higher-order case is more interesting.
    (contract [Int -> Int] (ambrose))
  Now I must provide a value that is a function taking and returning integers.

  In this transaction:
    - positive blame = Ambrose
    - negative blame = You

  Ok, what if I provide you with the value `42`?
  Not the correct shape, blame Ambrose.

  Ok, what if I provide you with the value `identity`?
  It definitely is the correct shape, but does it behave correctly?
  We must wrap this value thusly
    (fn [i]
      (contract Int (f i) :positive 'Ambrose))
  to check the return value of each invocation.

  Now if I provided `(fn [x] true)`, Ambrose is blamed for providing a value with
  incorrect *behaviour* (returning booleans instead of integers).

  When are *you* blamed?
  If you use the function incorrectly.
  eg. (let [f (contract [Int -> Int] identity)]
        (f nil))
      ; Blame *you*
  This is achieved by wrapping like so:
    (fn [i]
      (let [i (contract Int i :positive 'You)]
        (contract Int (f i) :positive 'Ambrose)))"
  '{:positive StrSym
    :negative StrSym})

(t/defalias FirstOrder
  "A first order predicate immediately checks its input without
  any need for wrapping.
  
  eg. First-order predicate for an integer predicate.
        integer?

      An imprecise, but best-effort first-order predicate for
      [Int -> Int] values:
        ifn?
  "
  [t/Any :-> t/Any])

(t/defalias Projection
  "A Projection is a curried function that first takes a blame
  object, then the actual value to check. The final return value is either

  - a possibly wrapped variant of the input value
  - a blame error using the given blame object
  
  eg. Projection for an integer contract.
      (fn [b]
        (fn [x]
          (if (integer? x)
            x
            (throw-blame b))))"
  [Blame :-> [t/Any :-> t/Any]])

(t/defalias Contract
  "A Contract represents a check on the shape and/or behaviour of a value.

  It has a first-order predicate that allow false positives (eg. ifn? for function
  contracts). Its Projection must only return a value if the new value is
  sufficiently protected such that the contract is enforced.
  
  eg. An integer contract
      {:first-order integer?
       :projection (fn [b]
                     (fn [x]
                       (if (integer? x)
                         x
                         (throw-blame b))))
       :name 'int-c}"
  '{:first-order FirstOrder
    :projection  Projection
    :name t/Sym})

(t/ann make-blame [& :optional {:positive (t/U nil t/Sym)
                                :negative (t/U nil t/Sym)}
                   :-> Blame])
(defn make-blame
  "Make a new blame object.
  
  If a blame party is missing, blame the \"unknown\" party."
  [& {:keys [positive negative]}]
  (let [positive (or positive
                     "unknown")
        negative (or negative
                     "unknown")]
    {:positive positive
     :negative negative}))

(t/defn throw-blame
  "Throws a blame object, blaming the positive party.
  
  Can distinguish a blame ExceptionInfo by {:blame true}
  in its ex-data."
  [{:keys [positive negative] :as b} :- Blame]
  (throw (ex-info (str "Contract error\n"
                       "Positive: " positive "\n"
                       "Negative: " negative)
                  {:blame true})))

(t/defn swap-blame [b :- Blame] :- Blame
  (-> b
      (assoc :positive (:negative b))
      (assoc :negative (:positive b))))

(t/ann make-contract [& :optional {:first-order (t/U nil FirstOrder)
                                   :projection  (t/U nil Projection)
                                   :name (t/U nil t/Sym)}
                      :-> Contract])
(defn make-contract
  "Make a new contract with optional first-order predicate,
  projection, and name.
  
  Default first-order predicate always returns true (returns true
  a least a many times as the contract passes, and probably more).
  
  Default projection simply uses the first-order predicate (possibly
  overridden) to check the value, and returns the value if true, otherwise
  blames the positive party.
  
  Default name is 'anonymous.
  
  eg. Integer contract
      (make-contract :name 'int-c
                     :first-order integer?)
      
      [Int -> Int] contract
      (make-contract
        :name 'int->int
        :first-order ifn? ;; allows false positives
        :projection (t/fn [b :- Blame]
                      (fn [f]
                        (fn [x]
                          (let [x (contract int-c x (swap-blame b))]
                            (contract int-c (f x)))))))
  "
  [& {:keys [first-order projection name]}]
  (let [name (or name
                 'anonymous)
        first-order (or first-order
                        (fn [x] true))
        projection (or projection
                       (t/fn [b :- Blame]
                         (t/fn [x :- t/Any]
                           (if (first-order x)
                             x
                             (throw-blame b)))))]
    {:first-order first-order
     :projection projection
     :name name}))

(def int-c 
  "An integer contract"
  (make-contract :name 'int-c
                 :first-order integer?))

#_(((:projection int-c)
  (make-blame))
 nil)

(defmacro contract 
  "Check a value against a contract, with optional blame.

  eg. Integer check
        (contract Int 1)

      [Int -> Int] check
        (contract [Int -> Int] identity)
  "
  ([c x] `(contract ~c ~x (make-blame)))
  ([c x b]
   `(((:projection ~c) ~b) ~x)))

(def int->int-c
  "Contract for [Int :-> Int] functions."
  (make-contract
    :name 'int->int
    :first-order ifn?
    :projection (t/fn [b :- Blame]
                  (fn [f]
                    (fn [x]
                      (let [x (contract int-c x (swap-blame b))]
                        (contract int-c ((t/cast [t/Any -> t/Any] f) x))))))))

(defmacro throws-blame? [& body]
  `(try (do ~@body)
        false
        (catch clojure.lang.ExceptionInfo e#
          (-> e# ex-data :blame boolean))))

(assert (= 1 (contract int-c 1)))
(assert (throws-blame? (contract int-c nil)))
(assert (= 1 ((t/cast [t/Any -> t/Any] (contract int->int-c identity)) 1)))
