import PaperILean.PublishedSemialgebraicCellDecomposition
import PaperILean.PublishedFiberFormatComponents

/-! The geometric zero-dimensional fiber application in I633/I638.

The source dimension is the largest dimension of an injective semialgebraic
open-cube map; the empty set has dimension -1. Cell decomposition proves that
nonpositive-dimensional sets are finite. A single component bound then also
bounds their cardinality. No replacement definition using finiteness or total
disconnectedness occurs. Mandatory quantifier-order and empty-set obstruction
tests passed in checkpoint_104_007_uniform_conditioning_obstructions_final.log.
-/

noncomputable section
namespace PaperI
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem projectionFiber_hasPolynomialSignDescription {ι κ : Type*}
    (S : Set ((ι ⊕ κ) → ℝ)) (hS : HasPolynomialSignDescription S) (p : ι → ℝ) :
    HasPolynomialSignDescription (projectionFiber S p) := by
  obtain ⟨A, hA⟩ := hS
  exact ⟨specializePolynomialFamily p A, polynomialSignDetermined_projectionFiber p A S hA⟩

/-- The integer N already bounding components also bounds points in every
geometrically nonpositive-dimensional set, including the empty set. -/
theorem published_card_bound_of_geometric_dimension_le_zero
    (hCells : PublishedSemialgebraicCellDecomposition)
    {α : Type} [Finite α] (S : Set (α → ℝ))
    (hS : HasPolynomialSignDescription S) {N : ℕ}
    (hN : Finite (ConnectedComponents S) ∧ Nat.card (ConnectedComponents S) ≤ N)
    {z : ℤ} (hdim : HasGeometricSemialgebraicDimension S z) (hz : z ≤ 0) :
    Finite S ∧ Nat.card S ≤ N := by
  letI : TotallyDisconnectedSpace S :=
    published_totallyDisconnected_of_geometric_dimension_le_zero hCells S hS hdim hz
  exact finite_and_card_le_of_totallyDisconnected hN

/-- One bound for a fixed actual family, simultaneously for all components and
for cardinalities of the geometrically zero-dimensional fibers. The dimension
≤0 form also handles empty fibers under the source's dimension -1 convention. -/
theorem published_projection_component_and_geometric_fiber_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {ι κ : Type} [Finite ι] [Finite κ]
    (S : Set ((ι ⊕ κ) → ℝ)) (hS : HasPolynomialSignDescription S) :
    ∃ N : ℕ, ∀ p : ι → ℝ,
      (Finite (ConnectedComponents (projectionFiber S p)) ∧
        Nat.card (ConnectedComponents (projectionFiber S p)) ≤ N) ∧
      ∀ z : ℤ, HasGeometricSemialgebraicDimension (projectionFiber S p) z → z ≤ 0 →
        Finite (projectionFiber S p) ∧ Nat.card (projectionFiber S p) ≤ N := by
  obtain ⟨N, hN⟩ :=
    published_projection_fiber_component_bound hCells.toFiniteConnectedCover hHardt hQE S hS
  refine ⟨N, ?_⟩
  intro p
  refine ⟨hN p, ?_⟩
  intro z hz hle
  exact published_card_bound_of_geometric_dimension_le_zero hCells (projectionFiber S p)
    (projectionFiber_hasPolynomialSignDescription S hS p) (hN p) hz hle

/-- Full coefficient and external-parameter uniformity at quantifier-free sign
format, with the same N for components and geometrically zero-dimensional
cardinality. It follows the source cell/triviality application. -/
theorem published_at_most_sign_format_component_and_geometric_fiber_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (n₀ s D : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≤ n₀ →
      ∀ (ι : Type) (A : Finset (MvPolynomial (ι ⊕ Fin n) ℝ))
        (S : Set ((ι ⊕ Fin n) → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ p : ι → ℝ,
      (Finite (ConnectedComponents (projectionFiber S p)) ∧
        Nat.card (ConnectedComponents (projectionFiber S p)) ≤ N) ∧
      ∀ z : ℤ, HasGeometricSemialgebraicDimension (projectionFiber S p) z → z ≤ 0 →
        Finite (projectionFiber S p) ∧ Nat.card (projectionFiber S p) ≤ N := by
  obtain ⟨N, hN⟩ := published_at_most_sign_format_projection_fiber_component_bound
    hCells.toFiniteConnectedCover hHardt hQE n₀ s D
  refine ⟨N, ?_⟩
  intro n hn ι A S hcard hdegree hS p
  have hp := hN n hn ι A S hcard hdegree hS p
  refine ⟨hp, ?_⟩
  intro z hz hle
  exact published_card_bound_of_geometric_dimension_le_zero hCells (projectionFiber S p)
    (projectionFiber_hasPolynomialSignDescription S ⟨A, hS⟩ p) hp hz hle

end PaperI
