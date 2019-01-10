;; activate model generation
(set-option :produce-models true)

;;%%%%
;Declaration of Goal, Assumption and Refinement Propostions
;%%%%
(declare-fun G1 () Bool) 
(declare-fun G2 () Bool) 
(declare-fun CCR1 () Bool) 


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
(assert (=> (G1 G2)))


(assert-soft G1 :id unsat_requirements)
(assert-soft G2 :id unsat_requirements)

    ;;%%
    ;;Optimization:
    ;;%%
    (minimize unsat_requirements)
    (check-sat)
    (set-model 1)
    (get-model)
    (exit)