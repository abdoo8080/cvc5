(set-logic ALL)
(set-info :status sat)

(declare-const x Bool)
(declare-fun c () Int)
(declare-fun c_ () Int)
(assert (or x (= 0 (+ c 1))))
(assert (or (exists ((v Int)) (str.<= "a" (str.substr "a" 0 v))) (= c_ (+ c_ c))))
(check-sat)
