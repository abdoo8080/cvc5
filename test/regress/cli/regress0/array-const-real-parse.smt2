; COMMAND-LINE: --arrays-exp --print-arith-lit-token
(set-logic QF_AUFLIRA)
(set-info :status sat)
(declare-fun a () (Array Int Real))
(assert (= a ((as const (Array Int Real)) 0.0)))
(declare-fun b () (Array Int Real))
(assert (= b ((as const (Array Int Real)) 1/3)))
(check-sat)
