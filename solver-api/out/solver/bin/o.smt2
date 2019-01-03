;; activate model generation
(set-option :produce-models true)

;;%%%%
;Declaration of Goal, Assumption and Refinement Propostions
;%%%%
(declare-fun G1 () Bool) 


;;%%%%
;Close-world
;%%%%


;;%%%%
;Refinement-Goal relationships
;%%%%


;;%%%%
;Mandatory goals
;%%%%


;;%%%%
;Contributions
;%%%%


(assert-soft G1 :id unsat_requirements)

;;%%
;;Optimization:
;;%%
(minimize unsat_requirements)
(minimize sat_tasks)
(check-sat)
(set-model 1)
(get-model)
(exit)