(set-logic ALL)
(set-info :status sat)
(declare-fun a () Int)
(declare-fun b (Int) Bool)
(declare-fun c (Int) Int)
(assert (= (c 0) (c 1)))
(assert (not (b 1)))
(assert (b ((_ iand 3) a 1)))
(check-sat)