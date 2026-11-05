import PaperILean.PublishedUniformAnalyticCuts
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple

/-! Coefficient-uniform original analytic cuts. A finite maximum over Boolean
sign tables is taken after applying the fixed-family theorem to universal
coefficient families, but before any coefficient, represented set, function or
endpoint. No continuity is needed for the open analytic pieces; closed-interval
variation still requires its separately retained continuity hypothesis. -/

noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
local instance analyticCutFinTwoDecidableEq : DecidableEq (Fin 2) := Classical.typeDecidableEq _

/-- Tuple-format bound before every coefficient, Boolean description and endpoint. -/
theorem published_bounded_tuple_analytic_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedPiecewiseNashExtensions) (s D : ℕ) :
    ∃ K : ℕ, ∀ (P : Fin s → MvPolynomial (Fin 2) ℝ),
      (∀ i, (P i).totalDegree ≤ D) → ∀ S : Set (Fin 2 → ℝ),
      PolynomialSignDetermined (Finset.univ.image P) S →
      ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        AnalyticOnCutIntervals f C ∧ C.card ≤ K := by
  classical
  have h := fun q : (Fin s → Bool × Bool) → Bool =>
    published_uniform_analytic_cut_sets hCell hHardt hQE hNash
      (universalPolynomialBooleanSet (Fin 2) s D q)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s D q))
  choose K hK using h
  refine ⟨Finset.univ.sup K, ?_⟩
  intro P hP S hS f a b hab hrep
  obtain ⟨q,hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D P hP S hS
  have hrep' : ∀ t ∈ Icc a b, ∀ y : ℝ,
      Sum.elim (polynomialFamilyCoefficients D P) ![t,y] ∈
        universalPolynomialBooleanSet (Fin 2) s D q ↔ y = f t := by
    intro t ht y
    simpa only [hEq,mem_setOf_eq] using hrep t ht y
  obtain ⟨C,ha,hb,hC,hA,hcard⟩ := hK q (polynomialFamilyCoefficients D P) f a b hab hrep'
  exact ⟨C,ha,hb,hC,hA,hcard.trans (Finset.le_sup (f := K) (Finset.mem_univ q))⟩

/-- At-most graph format, with zero, repeated and degree-dropping atoms allowed. -/
theorem published_bounded_sign_format_analytic_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedPiecewiseNashExtensions) (s D : ℕ) :
    ∃ K : ℕ, ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ P ∈ A, P.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        AnalyticOnCutIntervals f C ∧ C.card ≤ K := by
  obtain ⟨K,hK⟩ := published_bounded_tuple_analytic_cut_sets hCell hHardt hQE hNash s D
  refine ⟨K,?_⟩
  intro A S hcard hdegree hS f a b hab hrep
  obtain ⟨P,hP,hSP⟩ := exists_bounded_polynomial_tuple_of_signDetermined
    A S s D hcard hdegree hS
  exact hK P hP S hSP f a b hab hrep

end PaperI
