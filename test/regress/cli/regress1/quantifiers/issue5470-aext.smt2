; EXPECT: sat
; DISABLE-TESTER: model
(set-logic NIA)

(set-info :status sat)
(declare-fun b () Int)
(assert (exists ((c Int)) (< 0 c (div 0 b))))
(check-sat)
