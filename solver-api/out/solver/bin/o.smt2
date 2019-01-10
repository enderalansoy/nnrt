;; activate model generation
(set-option :produce-models true)

;;%%%%
;Declaration of Goal, Assumption and Refinement Propostions
;%%%%
(declare-fun G1 () Bool) 
(declare-fun G2 () Bool) 
(declare-fun G3 () Bool) 
(declare-fun G4 () Bool) 
(declare-fun G5 () Bool) 
(declare-fun R1 () Bool) 
(declare-fun R2 () Bool) 
(declare-fun R3 () Bool) 
(declare-fun CCR1 () Bool) 
(declare-fun CCR2 () Bool) 


;;%%%%
;Close-world
;%%%%

(assert (=> G2(or R3)))
(assert (=> G1(or R2  R1 )))


;;%%%%
;Refinement-Goal relationships
;%%%%
(assert (and (= R1 (and G2 )) (=> R1 G1 )))
(assert (and (= R2 (and G3 )) (=> R2 G1 )))
(assert (and (= R3 (and G5 G4 )) (=> R3 G2 )))


;;%%%%
;Mandatory goals
;%%%%
(assert G3)


;;%%%%
;Contributions
;%%%%
(assert (= CCR1 (and G5 G3)))
(assert-soft (not CCR1) :weight 3 :id PCC)
(assert (= CCR2 (and G2 G3)))
(assert-soft (not CCR2) :weight 2 :id PVC)


(assert-soft (not G3 ) :id sat_tasks)
(assert-soft (not G4 ) :id sat_tasks)
(assert-soft (not G5 ) :id sat_tasks)
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