(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status unsat)

(declare-const x Int)
(assert (str.contains (str.++ "some text" (str.from_int x) "tor") "vector"))
(check-sat)
