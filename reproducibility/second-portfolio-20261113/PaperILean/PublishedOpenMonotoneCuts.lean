import PaperILean.OpenGraphMonotonicity
import PaperILean.StrictCommonMonotonePartition
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple

/-! I1261: uniform coordinate-monotone subdivision on OPEN intervals.
The existing accepted qualitative monotonicity and finite-fiber counting inputs
remain explicit. No endpoint continuity or bounded range is assumed for cuts. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
local instance openCutFinTwoDecidableEq : DecidableEq (Fin 2) := Classical.typeDecidableEq _
set_option maxHeartbeats 1000000

theorem published_uniform_open_monotone_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ K : ℕ, ∀ (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ),
      a ≤ b → ContinuousOn f (Ioo a b) →
      (∀ t ∈ Ioo a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        MonotoneOnCutIntervals f C ∧ C.card ≤ K := by
  have hBad := hQE.finite_sign_description _ (graphMonotonicityBadRelation_definable hG)
  obtain ⟨N, hN⟩ := published_scalar_finite_fiber_card_bound
    hCell hHardt hQE (graphMonotonicityBadRelation G) hBad
  refine ⟨N + 2, ?_⟩
  intro p f a b hab hf hrep
  have hGraph := published_openScalarGraph_sign_description_open hQE hG p f a b hrep
  have hfin := published_monotonicityBadSet_finite hMono f a b hGraph
  have he := scalar_bad_fiber_eq_monotonicityBadSet_open G p f a b hrep
  have hcard : Nat.card (MonotonicityBadSet f a b) ≤ N := by
    have h := hN (Sum.elim p ![a,b]) (he.symm ▸ hfin)
    simpa only [he] using h
  obtain ⟨C, ha, hb, hC, hm, hc⟩ := exists_monotone_cut_set_of_finite_bad_set_open hab hf hfin
  exact ⟨C, ha, hb, hC, hm, hc.trans (Nat.add_le_add_right hcard 2)⟩

theorem published_bounded_tuple_open_monotone_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity) (s D : ℕ) :
    ∃ K : ℕ, ∀ (P : Fin s → MvPolynomial (Fin 2) ℝ),
      (∀ i, (P i).totalDegree ≤ D) → ∀ S : Set (Fin 2 → ℝ),
      PolynomialSignDetermined (Finset.univ.image P) S →
      ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn f (Ioo a b) →
      (∀ t ∈ Ioo a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        MonotoneOnCutIntervals f C ∧ C.card ≤ K := by
  classical
  have h := fun q : (Fin s → Bool × Bool) → Bool =>
    published_uniform_open_monotone_cut_sets hCell hHardt hQE hMono
      (universalPolynomialBooleanSet (Fin 2) s D q)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s D q))
  choose K hK using h
  refine ⟨Finset.univ.sup K, ?_⟩
  intro P hP S hS f a b hab hf hrep
  obtain ⟨q, hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D P hP S hS
  have hrep' : ∀ t ∈ Ioo a b, ∀ y : ℝ,
      Sum.elim (polynomialFamilyCoefficients D P) ![t,y] ∈
        universalPolynomialBooleanSet (Fin 2) s D q ↔ y = f t := by
    intro t ht y
    simpa only [hEq, mem_setOf_eq] using hrep t ht y
  obtain ⟨C, ha, hb, hC, hm, hc⟩ := hK q (polynomialFamilyCoefficients D P) f a b hab hf hrep'
  exact ⟨C, ha, hb, hC, hm, hc.trans (Finset.le_sup (f := K) (Finset.mem_univ q))⟩

/-- At-most sign format, including zero, repeated, or degree-dropping atoms. -/
theorem published_bounded_sign_format_open_monotone_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity) (s D : ℕ) :
    ∃ K : ℕ, ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ P ∈ A, P.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn f (Ioo a b) →
      (∀ t ∈ Ioo a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        MonotoneOnCutIntervals f C ∧ C.card ≤ K := by
  obtain ⟨K, hK⟩ := published_bounded_tuple_open_monotone_cut_sets hCell hHardt hQE hMono s D
  refine ⟨K, ?_⟩
  intro A S hcard hdegree hS f a b hab hf hrep
  obtain ⟨P, hP, hSP⟩ := exists_bounded_polynomial_tuple_of_signDetermined
    A S s D hcard hdegree hS
  exact hK P hP S hSP f a b hab hf hrep

/-- All functions and their possibly different sign descriptions follow one
bound. The finite number of functions is part of its allowed dependence. -/
theorem published_bounded_sign_format_strict_open_common_partition
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity)
    (ι : Type) [Fintype ι] (s D : ℕ) :
    ∃ M : ℕ, ∀ (f : ι → ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ i, ContinuousOn (f i) (Ioo a b)) →
      (∀ i, ∃ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
        A.card ≤ s ∧ (∀ P ∈ A, P.totalDegree ≤ D) ∧ PolynomialSignDetermined A S ∧
        ∀ t ∈ Ioo a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f i t) →
      ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ M ∧ t 0 = a ∧ t n = b ∧
        MonotoneOn t (Icc 0 n) ∧
        ∀ j < n, t j < t (j + 1) ∧ ∀ i, MonotoneOn (f i) (Ioo (t j) (t (j + 1))) ∨
          AntitoneOn (f i) (Ioo (t j) (t (j + 1))) := by
  obtain ⟨K, hK⟩ := published_bounded_sign_format_open_monotone_cut_sets hCell hHardt hQE hMono s D
  refine ⟨1 + ∑ _ : ι, K, ?_⟩
  intro f a b hab hf hgraph
  apply exists_strict_common_partition_of_individual_subdivisions f (fun _ => K) hab
  intro i
  obtain ⟨A, S, hcard, hdeg, hS, hrep⟩ := hgraph i
  exact hK A S hcard hdeg hS (f i) a b hab (hf i) hrep

end PaperI

