(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var d Int)

(rule (inv x 0))

(rule (=> 
    (and 
        (inv x d)
        (>= x 0)
        (= x1 (+ x d))
    )
    (inv x1 d)
  )
)