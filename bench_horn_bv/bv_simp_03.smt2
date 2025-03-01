(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var c (_ BitVec 16))
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var c1 (_ BitVec 16))

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))

(rule (=> (and (= #x0000 (bvand b #x0001)) (= a c)) (inv a b c)))

(rule (=>
  (and
    (inv a b c)
    (not (= b #x0000))
    (= a1 a)
    (= c1 (bvneg c))
    (= b1 (bvsub b #x0001)))
  (inv a1 b1 c1)))

(rule (=> (and (inv a b c) (= #x0000 (bvand b #x0001)) (not (= a c))) fail))

(query fail)
