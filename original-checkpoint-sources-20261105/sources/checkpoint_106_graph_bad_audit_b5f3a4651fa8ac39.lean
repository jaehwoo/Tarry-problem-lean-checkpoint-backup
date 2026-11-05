import PaperILean.GraphMonotonicityRealization

#check PaperI.MonotonicityBase
#print axioms PaperI.MonotonicityBase
#check PaperI.MonotonicityWindow
#print axioms PaperI.MonotonicityWindow
#check PaperI.graphIntervalCondition
#print axioms PaperI.graphIntervalCondition
#check PaperI.realCoordinate_lt_definable
#print axioms PaperI.realCoordinate_lt_definable
#check PaperI.realCoordinate_eq_definable
#print axioms PaperI.realCoordinate_eq_definable
#check PaperI.graphIntervalCondition_definable
#print axioms PaperI.graphIntervalCondition_definable
#check PaperI.increasingGraphComparisons
#print axioms PaperI.increasingGraphComparisons
#check PaperI.decreasingGraphComparisons
#print axioms PaperI.decreasingGraphComparisons
#check PaperI.constantGraphComparisons
#print axioms PaperI.constantGraphComparisons
#check PaperI.graphMonotonicityGoodRelation
#print axioms PaperI.graphMonotonicityGoodRelation
#check PaperI.graphMonotonicityBadRelation
#print axioms PaperI.graphMonotonicityBadRelation
#check PaperI.graphMonotonicityGoodRelation_definable
#print axioms PaperI.graphMonotonicityGoodRelation_definable
#check PaperI.graphMonotonicityBadRelation_definable
#print axioms PaperI.graphMonotonicityBadRelation_definable
#check PaperI.graphIntervalCondition_realize_iff
#print axioms PaperI.graphIntervalCondition_realize_iff
#check PaperI.graphMonotonicityGoodRelation_realize_iff
#print axioms PaperI.graphMonotonicityGoodRelation_realize_iff
#check PaperI.graphMonotonicityBadRelation_realize_iff
#print axioms PaperI.graphMonotonicityBadRelation_realize_iff

open PaperI Set
example (a b x : ℝ) :
    Sum.elim (Sum.elim (fun _ : Unit => (0 : ℝ)) ![a,b]) (fun _ : Unit => x) ∈
      graphMonotonicityBadRelation {v : (Unit ⊕ Fin 2) → ℝ | v (Sum.inr 1) = v (Sum.inr 0)} ↔
      x ∈ MonotonicityBadSet (fun t => t) a b := by
  apply graphMonotonicityBadRelation_realize_iff
  intro t ht y
  rfl
example (a x : ℝ) : x ∉ MonotonicityBadSet (fun _ => (7 : ℝ)) a a := by
  simp [MonotonicityBadSet]
example (a b x : ℝ) :
    Sum.elim (Sum.elim (fun _ : Unit => (0 : ℝ)) ![a,b]) (fun _ : Unit => x) ∈
      graphMonotonicityBadRelation {v : (Unit ⊕ Fin 2) → ℝ | v (Sum.inr 1) = 7} ↔
      x ∈ MonotonicityBadSet (fun _ => 7) a b := by
  apply graphMonotonicityBadRelation_realize_iff
  intro t ht y
  rfl
