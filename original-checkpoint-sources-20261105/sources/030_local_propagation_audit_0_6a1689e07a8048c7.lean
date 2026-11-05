import PaperILean.LocalMonotonicityPropagation
#check PaperI.LocalIntervalLocus
#print axioms PaperI.LocalIntervalLocus
#check PaperI.isOpen_localIntervalLocus
#print axioms PaperI.isOpen_localIntervalLocus
#check PaperI.disjoint_local_strictMono_strictAnti
#print axioms PaperI.disjoint_local_strictMono_strictAnti
#check PaperI.disjoint_local_strictMono_constant
#print axioms PaperI.disjoint_local_strictMono_constant
#check PaperI.disjoint_local_strictAnti_constant
#print axioms PaperI.disjoint_local_strictAnti_constant
#check PaperI.monotoneOn_of_local_strictMono
#print axioms PaperI.monotoneOn_of_local_strictMono
#check PaperI.antitoneOn_of_local_strictAnti
#print axioms PaperI.antitoneOn_of_local_strictAnti
#check PaperI.eqOn_of_local_constant
#print axioms PaperI.eqOn_of_local_constant
#check PaperI.monotoneOn_or_antitoneOn_of_no_bad_points
#print axioms PaperI.monotoneOn_or_antitoneOn_of_no_bad_points
open Set PaperI
example (f : ℝ → ℝ) (a : ℝ) : MonotoneOn f (Ioo a a) := by
  intro x hx
  exact (lt_irrefl a (hx.1.trans hx.2)).elim
example (a b c x : ℝ) (hx : x ∈ Ioo a b) :
    LocalStrictMonotoneOrConstant (fun _ => c) a b x :=
  ⟨a, b, le_rfl, le_rfl, hx.1, hx.2, Or.inr (Or.inr (fun _ _ => rfl))⟩
