import PaperILean.PolynomialFiberFormat
import PaperILean.PublishedFormatComponents

/-! The combined format-uniform application to actual fibers. The bound is
chosen before all base parameters and polynomial coefficients. These are
quantifier-free polynomial-sign format statements; the geometric dimension
zero and arbitrary quantified input-format bridges remain separate. -/

noncomputable section
namespace PaperI
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem published_bounded_sign_format_projection_fiber_component_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (κ : Type) [Fintype κ] (s D : ℕ) :
    ∃ N : ℕ, ∀ (ι : Type) (A : Finset (MvPolynomial (ι ⊕ κ) ℝ))
      (S : Set ((ι ⊕ κ) → ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ p : ι → ℝ, Finite (ConnectedComponents (projectionFiber S p)) ∧
        Nat.card (ConnectedComponents (projectionFiber S p)) ≤ N := by
  obtain ⟨N, hN⟩ := published_bounded_sign_format_component_bound hCell hHardt hQE κ s D
  refine ⟨N, ?_⟩
  intro ι A S hcard hdegree hS p
  obtain ⟨B, hBc, hBd, hBS⟩ :=
    projectionFiber_has_bounded_sign_format p A S s D hcard hdegree hS
  exact hN B (projectionFiber S p) hBc hBd hBS

/-- The usual bounded variable count, with N preceding all dimensions, base
variables, coefficients, Boolean descriptions and external parameter values. -/
theorem published_at_most_sign_format_projection_fiber_component_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (n₀ s D : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≤ n₀ →
      ∀ (ι : Type) (A : Finset (MvPolynomial (ι ⊕ Fin n) ℝ))
      (S : Set ((ι ⊕ Fin n) → ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ p : ι → ℝ, Finite (ConnectedComponents (projectionFiber S p)) ∧
        Nat.card (ConnectedComponents (projectionFiber S p)) ≤ N := by
  obtain ⟨N, hN⟩ := published_at_most_sign_format_component_bound hCell hHardt hQE n₀ s D
  refine ⟨N, ?_⟩
  intro n hn ι A S hcard hdegree hS p
  obtain ⟨B, hBc, hBd, hBS⟩ :=
    projectionFiber_has_bounded_sign_format p A S s D hcard hdegree hS
  exact hN n hn B (projectionFiber S p) hBc hBd hBS

/-- Topological cardinality consequence with the same coefficient-uniform
format bound. Total disconnectedness is retained as a hypothesis. -/
theorem published_at_most_sign_format_totallyDisconnected_fiber_card_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (n₀ s D : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≤ n₀ →
      ∀ (ι : Type) (A : Finset (MvPolynomial (ι ⊕ Fin n) ℝ))
      (S : Set ((ι ⊕ Fin n) → ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ p : ι → ℝ, TotallyDisconnectedSpace (projectionFiber S p) →
        Finite (projectionFiber S p) ∧ Nat.card (projectionFiber S p) ≤ N := by
  obtain ⟨N, hN⟩ :=
    published_at_most_sign_format_projection_fiber_component_bound hCell hHardt hQE n₀ s D
  refine ⟨N, ?_⟩
  intro n hn ι A S hcard hdegree hS p hp
  letI : TotallyDisconnectedSpace (projectionFiber S p) := hp
  exact finite_and_card_le_of_totallyDisconnected (hN n hn ι A S hcard hdegree hS p)

end PaperI
