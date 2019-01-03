;; activate model generation
(set-option :produce-models true)

;;%%%%
;Declaration of Goal, Assumption and Refinement Propostions
;%%%%
(declare-fun G1 () Bool) 
(declare-fun G2 () Bool) 
(declare-fun R1 () Bool) 


;;%%%%
;Close-world
;%%%%

(assert (=> G1(or R1)))


;;%%%%
;Refinement-Goal relationships
;%%%%
(assert (and (= R1 (and G2 )) (=> R1 G1 )))


;;%%%%
;Mandatory goals
;%%%%


;;%%%%
;Contributions
;%%%%


;;%%
;;Optimization:
;;%%
(minimize unsat_requirements)
(minimize sat_tasks)
(check-sat)
(get-model)
(exit)
