import PaperILean.DerivativeSignCutConstruction

/-! Uniform actual derivative-sign cuts over bounded scalar graph format.
Universal coefficient families and a finite maximum over Boolean tables place
the cut bound before all real coefficients, represented functions and endpoints.
These are differentiable/sign cuts; analyticity requires the separate checked
analytic subdivision and refinement, not an inference from derivative signs. -/

noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
local instance derivativeSignFinTwoDecidableEq : DecidableEq (Fin 2) := Classical.typeDecidableEq _

theorem published_bounded_tuple_derivative_sign_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    (s D : ℕ) :
    ∃ K : ℕ, ∀ (P : Fin s → MvPolynomial (Fin 2) ℝ),
      (∀ i, (P i).totalDegree ≤ D) → ∀ S : Set (Fin 2 → ℝ),
      PolynomialSignDetermined (Finset.univ.image P) S →
      ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧ C.card ≤ K ∧
        ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          DifferentiableOn ℝ f (Ioo u v) ∧ DerivativeSignOn f (Ioo u v) := by
  classical
  have h := fun q : (Fin s → Bool × Bool) → Bool =>
    published_uniform_derivative_sign_cut_sets hCell hHardt hQE hNash
      (universalPolynomialBooleanSet (Fin 2) s D q)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s D q))
  choose K hK using h
  refine ⟨Finset.univ.sup K,?_⟩
  intro P hP S hS f a b hab hrep
  obtain ⟨q,hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D P hP S hS
  have hrep' : ∀ t ∈ Icc a b, ∀ y : ℝ,
      Sum.elim (polynomialFamilyCoefficients D P) ![t,y] ∈
        universalPolynomialBooleanSet (Fin 2) s D q ↔ y = f t := by
    intro t ht y
    simpa only [hEq,mem_setOf_eq] using hrep t ht y
  obtain ⟨C,ha,hb,hC,hcard,hcells⟩ := hK q (polynomialFamilyCoefficients D P) f a b hab hrep'
  exact ⟨C,ha,hb,hC,hcard.trans (Finset.le_sup (f := K) (Finset.mem_univ q)),hcells⟩

theorem published_bounded_sign_format_derivative_sign_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    (s D : ℕ) :
    ∃ K : ℕ, ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ P ∈ A, P.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧ C.card ≤ K ∧
        ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          DifferentiableOn ℝ f (Ioo u v) ∧ DerivativeSignOn f (Ioo u v) := by
  obtain ⟨K,hK⟩ := published_bounded_tuple_derivative_sign_cut_sets hCell hHardt hQE hNash s D
  refine ⟨K,?_⟩
  intro A S hcard hdeg hS f a b hab hrep
  obtain ⟨P,hP,hSP⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hcard hdeg hS
  exact hK P hP S hSP f a b hab hrep

end PaperI
