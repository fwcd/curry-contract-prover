; SMT script to verify precondition of 'fac' in function 'f'

; disable model-based quantifier instantiation (avoid loops)
(set-option :smt.mbqi false)

; For polymorphic types:
(declare-sort TVar 0)

; For functional types:
(declare-datatypes (T1 T2) ((Func (mk-func (argument T1) (result T2)))))




; Free variables:

; Boolean formula of assertion (known properties):
(assert true)

; Bindings of implication:
(assert true)

; Assert negated implication:
(assert (not (>= x1 0)))

; check satisfiability:
(check-sat)
; if unsat, we can omit this part of the contract check
