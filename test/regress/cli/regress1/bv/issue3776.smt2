(set-logic QF_UFBVLIA)
(set-info :status sat)
(declare-fun t () Int)
(assert (= t (ubv_to_int ((_ int_to_bv 1) t))))
(check-sat)
