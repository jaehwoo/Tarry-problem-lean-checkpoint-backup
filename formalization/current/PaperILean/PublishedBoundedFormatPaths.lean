import PaperILean.PublishedEndpointPaths
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple

/-! Uniform graph format for connected sets of bounded polynomial-sign format.
The path graph count and degree depend only on the fixed coordinate space,
input count and input degree. They precede all coefficients, Boolean choices,
sets, connectedness hypotheses and endpoints. This is obtained by a finite
maximum over universal coefficient families, not assumed as a published input.
Analytic subdivision remains a separate assertion. -/

noncomputable section
namespace PaperI
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem published_bounded_tuple_path_format
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (κ : Type) [Fintype κ] (s D : ℕ) :
    ∃ sPath dPath : ℕ, ∀ (P : Fin s → MvPolynomial κ ℝ),
      (∀ i, (P i).totalDegree ≤ D) → ∀ S : Set (κ → ℝ),
      PolynomialSignDetermined (Finset.univ.image P) S → IsPreconnected S →
      ∀ a ∈ S, ∀ b ∈ S, ∃ γ : SemialgebraicUnitPath S a b,
      ∃ B : Finset (MvPolynomial (Unit ⊕ κ) ℝ), B.card ≤ sPath ∧
        (∀ q ∈ B, q.totalDegree ≤ dPath) ∧
        PolynomialSignDetermined B (unitPathGraph γ.toFun) := by
  classical
  have h := fun q : (Fin s → Bool × Bool) → Bool =>
    published_family_uniform_endpoint_path_format hPath hHardt hQE
      (universalPolynomialBooleanSet κ s D q)
      (universalPolynomialBooleanSet_hasPolynomialSignDescription κ s D q)
  choose sPath dPath hPathFormat using h
  refine ⟨Finset.univ.sup sPath, Finset.univ.sup dPath, ?_⟩
  intro P hP S hS hc a ha b hb
  obtain ⟨q, hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D P hP S hS
  have hEq' : S = projectionFiber (universalPolynomialBooleanSet κ s D q)
      (polynomialFamilyCoefficients D P) := hEq
  rw [hEq'] at hc ha hb ⊢
  obtain ⟨γ, B, hs, hd, hB⟩ := hPathFormat q (polynomialFamilyCoefficients D P) hc a ha b hb
  exact ⟨γ, B, hs.trans (Finset.le_sup (f := sPath) (Finset.mem_univ q)),
    fun q' hq' => (hd q' hq').trans (Finset.le_sup (f := dPath) (Finset.mem_univ q)), hB⟩

/-- At-most input format, including empty lists, zero atoms, repetitions,
coefficient cancellation and degree drops. Endpoint equality is permitted. -/
theorem published_bounded_sign_format_paths
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (κ : Type) [Fintype κ] (s D : ℕ) :
    ∃ sPath dPath : ℕ, ∀ (A : Finset (MvPolynomial κ ℝ)) (S : Set (κ → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A S → IsPreconnected S →
      ∀ a ∈ S, ∀ b ∈ S, ∃ γ : SemialgebraicUnitPath S a b,
      ∃ B : Finset (MvPolynomial (Unit ⊕ κ) ℝ), B.card ≤ sPath ∧
        (∀ q ∈ B, q.totalDegree ≤ dPath) ∧
        PolynomialSignDetermined B (unitPathGraph γ.toFun) := by
  obtain ⟨sPath, dPath, h⟩ := published_bounded_tuple_path_format hPath hHardt hQE κ s D
  refine ⟨sPath, dPath, ?_⟩
  intro A S hcard hdeg hS hc a ha b hb
  obtain ⟨P, hP, hSP⟩ := exists_bounded_polynomial_tuple_of_signDetermined
    A S s D hcard hdeg hS
  exact h P hP S hSP hc a ha b hb

end PaperI
