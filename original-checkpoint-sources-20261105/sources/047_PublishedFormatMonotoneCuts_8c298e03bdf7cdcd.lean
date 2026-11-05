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

/-- At-most sign format, including zero, repeated, or degree-dropping atoms. -/
theorem published_bounded_sign_format_monotone_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity) (s D : ℕ) :
    ∃ K : ℕ, ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ P ∈ A, P.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn f (Icc a b) →
      (∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        MonotoneOnCutIntervals f C ∧ C.card ≤ K := by
  obtain ⟨K, hK⟩ := published_bounded_tuple_monotone_cut_sets hCell hHardt hQE hMono s D
  refine ⟨K, ?_⟩
  intro A S hcard hdegree hS f a b hab hf hrep
  obtain ⟨P, hP, hSP⟩ := exists_bounded_polynomial_tuple_of_signDetermined
    A S s D hcard hdegree hS
  exact hK P hP S hSP f a b hab hf hrep

/-- All functions and their possibly different sign descriptions follow one
bound. The finite number of functions is part of its allowed dependence. -/
theorem published_bounded_sign_format_common_partition
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity)
    (ι : Type) [Fintype ι] (s D : ℕ) :
    ∃ M : ℕ, ∀ (f : ι → ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ i, ContinuousOn (f i) (Icc a b)) →
      (∀ i, ∃ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
        A.card ≤ s ∧ (∀ P ∈ A, P.totalDegree ≤ D) ∧ PolynomialSignDetermined A S ∧
        ∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f i t) →
      ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ M ∧ t 0 = a ∧ t n = b ∧
        MonotoneOn t (Icc 0 n) ∧
        ∀ j < n, ∀ i, MonotoneOn (f i) (Ioo (t j) (t (j + 1))) ∨
          AntitoneOn (f i) (Ioo (t j) (t (j + 1))) := by
  obtain ⟨K, hK⟩ := published_bounded_sign_format_monotone_cut_sets hCell hHardt hQE hMono s D
  refine ⟨1 + ∑ _ : ι, K, ?_⟩
  intro f a b hab hf hgraph
  apply exists_common_partition_of_individual_subdivisions f (fun _ => K) hab
  intro i
  obtain ⟨A, S, hcard, hdeg, hS, hrep⟩ := hgraph i
  exact hK A S hcard hdeg hS (f i) a b hab (hf i) hrep

/-- Actual total variation, uniformly over coefficients, functions, endpoints,
and range lengths. This is not a project-specific external assumption. -/
theorem published_bounded_sign_format_variation
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity)
    (ι : Type) [Fintype ι] (s D : ℕ) :
    ∃ M : ℕ, ∀ (f : ι → ℝ → ℝ) (a b : ℝ) (B : ι → ℝ), a ≤ b →
      (∀ i, ContinuousOn (f i) (Icc a b)) →
      (∀ i, ∃ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
        A.card ≤ s ∧ (∀ P ∈ A, P.totalDegree ≤ D) ∧ PolynomialSignDetermined A S ∧
        ∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f i t) →
      (∀ i, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f i x - f i y| ≤ B i) →
      ∀ i, BoundedVariationOn (f i) (Icc a b) ∧
        variationOnFromTo (f i) Set.univ a b ≤ (M : ℝ) * B i := by
  obtain ⟨M, hM⟩ := published_bounded_sign_format_common_partition hCell hHardt hQE hMono ι s D
  refine ⟨M, ?_⟩
  intro f a b B hab hf hgraph hB
  obtain ⟨n, t, hn, ht0, htn, ht, hm⟩ := hM f a b hab hf hgraph
  have h := family_variation_le_of_bounded_common_partition f B M t n hn ht
    (by simpa only [ht0, htn] using hf) hm (by simpa only [ht0, htn] using hB)
  simpa only [ht0, htn] using h

end PaperI
