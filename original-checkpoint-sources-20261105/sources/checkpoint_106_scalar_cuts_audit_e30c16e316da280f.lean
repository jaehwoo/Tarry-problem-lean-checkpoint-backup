import PaperILean.PublishedScalarMonotonicity
import PaperILean.PublishedScalarFiniteFibers
import PaperILean.FiniteMonotonicityCuts

set_option pp.proofs false

#print PaperI.LocalStrictMonotoneOrConstant
#print axioms PaperI.LocalStrictMonotoneOrConstant

#print PaperI.MonotonicityBadSet
#print axioms PaperI.MonotonicityBadSet

#print PaperI.localStrictMonotoneOrConstant_mem_Ioo
#print axioms PaperI.localStrictMonotoneOrConstant_mem_Ioo

#print PaperI.monotonicityBadSet_subset_Ioo
#print axioms PaperI.monotonicityBadSet_subset_Ioo

#print PaperI.not_mem_monotonicityBadSet_iff
#print axioms PaperI.not_mem_monotonicityBadSet_iff

#print PaperI.openScalarGraph
#print axioms PaperI.openScalarGraph

#print PaperI.StrictMonotoneOnCutIntervals
#print axioms PaperI.StrictMonotoneOnCutIntervals

#print PaperI.PublishedOneVariableMonotonicity
#print axioms PaperI.PublishedOneVariableMonotonicity

#print PaperI.PublishedOneVariableMonotonicity.mk
#print axioms PaperI.PublishedOneVariableMonotonicity.mk

#print PaperI.PublishedOneVariableMonotonicity.finite_strict_subdivision
#print axioms PaperI.PublishedOneVariableMonotonicity.finite_strict_subdivision

#print PaperI.exists_consecutive_cuts_around_point
#print axioms PaperI.exists_consecutive_cuts_around_point

#print PaperI.monotonicityBadSet_subset_of_strict_cut_intervals
#print axioms PaperI.monotonicityBadSet_subset_of_strict_cut_intervals

#print PaperI.published_monotonicityBadSet_finite
#print axioms PaperI.published_monotonicityBadSet_finite

#print PaperI.scalarProjectionFiber
#print axioms PaperI.scalarProjectionFiber

#print PaperI.projectionFiberUnitEquivScalar
#print axioms PaperI.projectionFiberUnitEquivScalar

#print PaperI.published_scalar_finite_fiber_card_bound
#print axioms PaperI.published_scalar_finite_fiber_card_bound

#print PaperI.exists_monotone_cut_set_of_finite_bad_set
#print axioms PaperI.exists_monotone_cut_set_of_finite_bad_set

-- Executed boundary examples: constant function and degenerate interval.
example (c a b : ℝ) : PaperI.MonotonicityBadSet (fun _ => c) a b = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  exact hx.2 ⟨a, b, le_rfl, le_rfl, hx.1.1, hx.1.2,
    Or.inr (Or.inr (fun _ _ => rfl))⟩

example (f : ℝ → ℝ) (a : ℝ) : PaperI.MonotonicityBadSet f a a = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  exact (not_lt_of_ge hx.1.1.le) hx.1.2
