;; activate model generation
(set-option :produce-models true)

;;%%%%
;Declaration of Goal, Assumption and Refinement Propostions
;%%%%


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



;;%%
;;Preference:

;;%%
;;Optimization:
;;%%
(minimize unsat_requirements)
(minimize sat_tasks)
(check-sat)
(set-model 1)
(get-model)
(exit)

