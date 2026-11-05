import PaperILean.PublishedUniformMonotoneCuts
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple

/-! Coefficient-uniform monotonicity cuts, common partitions, and variation for
bounded scalar graph sign format. A finite maximum over Boolean tables and the
universal coefficient construction place the bound before all coefficients,
represented functions, intervals, and range lengths. The graph representation
is required only on the indicated closed interval. This verifies the scalar
monotonicity/variation part using accepted qualitative monotonicity and Hardt
inputs; constructing a bounded-format path remains a distinct prerequisite. -/

noncomputable section
set_option diagnostics true
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The integer depends only on the fixed graph coordinate dimension two,
polynomial count, and degree, before coefficients or Boolean descriptions. -/
theorem published_bounded_tuple_monotone_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity) (s D : ℕ) :
    ∃ K : ℕ, ∀ (P : Fin s → MvPolynomial (Fin 2) ℝ),
      (∀ i, (P i).totalDegree ≤ D) → ∀ S : Set (Fin 2 → ℝ),
      PolynomialSignDetermined (Finset.univ.image P) S →
      ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn f (Icc a b) →
      (∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        MonotoneOnCutIntervals f C ∧ C.card ≤ K := by
  classical
  have h := fun q : (Fin s → Bool × Bool) → Bool =>
    published_uniform_monotone_cut_sets hCell hHardt hQE hMono
      (universalPolynomialBooleanSet (Fin 2) s D q)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s D q))
  choose K hK using h
  refine ⟨Finset.univ.sup K, ?_⟩
  intro P hP S hS f a b hab hf hrep
  obtain ⟨q, hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D P hP S hS
  have hrep' : ∀ t ∈ Icc a b, ∀ y : ℝ,
      Sum.elim (polynomialFamilyCoefficients D P) ![t,y] ∈
        universalPolynomialBooleanSet (Fin 2) s D q ↔ y = f t := by
    intro t ht y
    simpa only [hEq, mem_setOf_eq] using hrep t ht y
  obtain ⟨C, ha, hb, hC, hm, hc⟩ := hK q (polynomialFamilyCoefficients D P) f a b hab hf hrep'
  exact ⟨C, ha, hb, hC, hm, hc.trans (Finset.le_sup (f := K) (Finset.mem_univ q))⟩


end PaperI
