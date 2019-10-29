(declare-rel f ((_ BitVec 16) ))
(declare-rel g ((_ BitVec 16) ))
(declare-rel h ((_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())
(declare-var x (_ BitVec 16))
(declare-var r0 (_ BitVec 16))
(declare-var r1 (_ BitVec 16))

(rule (=> (= r0 (bvadd x #x0001)) (h x r0)))
(rule (g #x0003))
(rule (=> (and (g r0) (h r0 r1)) (f r1)))
(rule (=> (and (f r1) (bvugt r1 #x0004)) fail))

(query fail)
