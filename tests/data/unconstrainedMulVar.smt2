(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info :status unsat)
(declare-fun s () (_ BitVec 8))
(declare-fun t () (_ BitVec 8))

(assert (and (or (not (= s #x00)) (bvsle s t))
                (forall ((x (_ BitVec 8))) (bvslt t (bvmul s x)))))
(check-sat)
(exit)
