import PaperILean.ClosedArcGraphFormat

/-! Uniform closure and endpoint-graph format from the ORIGINAL input format.
The output bounds are chosen before coefficients, endpoints and the curve.
No quantitative bound on the number of arc charts is asserted. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
set_option maxHeartbeats 1000000

theorem published_closureFamily_uniform_format
    (hQE : PublishedRealSemialgebraicity) {ρ α : Type} [Finite ρ] [Fintype α]
    (C : Set ((ρ ⊕ α) → ℝ)) (hC : (univ : Set ℝ).Definable Language.ring C) :
    ∃ s D : ℕ, ∀ p : ρ → ℝ, ∃ A : Finset (MvPolynomial α ℝ), A.card ≤ s ∧
      (∀ q ∈ A, q.totalDegree ≤ D) ∧ PolynomialSignDetermined A (closure (projectionFiber C p)) := by
  obtain ⟨s, D, h⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format
    (hQE.finite_sign_description _ (fiberClosureRelation_definable hC))
  exact ⟨s, D, fun p => h p⟩

theorem published_bounded_tuple_closure_format
    (hQE : PublishedRealSemialgebraicity) (α : Type) [Fintype α] (s D : ℕ) :
    ∃ sOut dOut : ℕ, ∀ p : Fin s → MvPolynomial α ℝ,
      (∀ i, (p i).totalDegree ≤ D) → ∀ S : Set (α → ℝ),
      PolynomialSignDetermined (Finset.univ.image p) S →
      ∃ B : Finset (MvPolynomial α ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined B (closure S) := by
  classical
  have h := fun b : (Fin s → Bool × Bool) → Bool =>
    published_closureFamily_uniform_format hQE (universalPolynomialBooleanSet α s D b)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription α s D b))
  choose sOut dOut hOut using h
  refine ⟨Finset.univ.sup sOut, Finset.univ.sup dOut, ?_⟩
  intro p hp S hS
  obtain ⟨b, hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D p hp S hS
  obtain ⟨B, hBc, hBd, hBS⟩ := hOut b (polynomialFamilyCoefficients D p)
  refine ⟨B, hBc.trans (Finset.le_sup (f := sOut) (Finset.mem_univ b)),
    fun q hq => (hBd q hq).trans (Finset.le_sup (f := dOut) (Finset.mem_univ b)), ?_⟩
  simpa only [hEq, projectionFiber] using hBS

theorem published_bounded_sign_format_closure_format
    (hQE : PublishedRealSemialgebraicity) (α : Type) [Fintype α] (s D : ℕ) :
    ∃ sOut dOut : ℕ, ∀ (A : Finset (MvPolynomial α ℝ)) (S : Set (α → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∃ B : Finset (MvPolynomial α ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined B (closure S) := by
  obtain ⟨sOut, dOut, h⟩ := published_bounded_tuple_closure_format hQE α s D
  refine ⟨sOut, dOut, ?_⟩
  intro A S hc hd hS
  obtain ⟨p, hp, hSp⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hc hd hS
  exact h p hp S hSp

/-- The original open-arc input format controls the closed extension format.
Neither the chosen endpoint limits nor the interval can affect the bounds. -/
theorem published_uniform_closedMonotoneArc_graph_format
    (hQE : PublishedRealSemialgebraicity) (κ : Type) [Fintype κ] (s D : ℕ) :
    ∃ sOut dOut : ℕ, ∀ (γ : ℝ → κ → ℝ) (a b : ℝ), a < b →
      ContinuousOn γ (Ioo a b) →
      (∀ i, MonotoneOn (fun t => γ t i) (Ioo a b) ∨
        AntitoneOn (fun t => γ t i) (Ioo a b)) →
      (∀ i, BddBelow ((fun t => γ t i) '' Ioo a b)) →
      (∀ i, BddAbove ((fun t => γ t i) '' Ioo a b)) →
      ∀ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A (parametrizedArcGraph γ (Ioo a b)) →
      ∃ B : Finset (MvPolynomial (Unit ⊕ κ) ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined B
          (parametrizedArcGraph (closedMonotoneArc γ a b) (Icc a b)) := by
  obtain ⟨sOut, dOut, h⟩ := published_bounded_sign_format_closure_format hQE (Unit ⊕ κ) s D
  refine ⟨sOut, dOut, ?_⟩
  intro γ a b hab hc hm hlo hhi A hAc hAd hA
  rw [closedMonotoneArc_graph_eq_closure hab hc hm hlo hhi]
  exact h A _ hAc hAd hA

end PaperI
