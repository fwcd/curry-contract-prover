; SMT script to verify precondition of 'fac' in function 'fac'

; disable model-based quantifier instantiation (avoid loops)
(set-option :smt.mbqi false)

; For polymorphic types:
(declare-sort TVar 0)

; For functional types:
(declare-datatypes (T1 T2) ((Func (mk-func (argument T1) (result T2)))))




; Free variables:
(declare-const x7 Int)
(declare-const x6 Int)
(declare-const x2 Bool)
(declare-const x3 Int)

; Boolean formula of assertion (known properties):
(assert (and (>= x1 0) (= x3 0) (= x2 (= x1 x3)) (= x2 true) (= x2 false)))

; Bindings of implication:
(assert (and (= x7 1) (= x6 (- x1 x7))))

; Assert negated implication:
(assert (not (>= x6 0)))

; check satisfiability:
(check-sat)
; if unsat, we can omit this part of the contract check
