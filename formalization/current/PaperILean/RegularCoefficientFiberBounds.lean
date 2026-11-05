import PaperILean.RegularCoefficientFiberTopology
import PaperILean.PublishedRawFormulaConditioning

/-! I658/I662/I665: uniform finite fibers of selected regular coefficient maps.
The joint graph retains the external parameter, output, selected domain and
input exactly. A fixed raw defining formula gives one N before all named real
coefficient values and all represented maps/domains. No finite-fiber or fake
zero-dimensionality hypothesis is assumed. The measure/area/Fubini conclusion
of I660/I662 is a subsequent, separate obligation. -/

noncomputable section
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- Joint relation of selected inputs and their actual output, with all
external parameters included as base coordinates. -/
def regularCoefficientGraph {ι κ : Type}
    (Ω : (ι → ℝ) → Set (κ → ℝ)) (T : (ι → ℝ) → (κ → ℝ) → (κ → ℝ)) :
    Set (((ι ⊕ κ) ⊕ κ) → ℝ) :=
  {v | (fun j => v (Sum.inr j)) ∈ Ω (fun i => v (Sum.inl (Sum.inl i))) ∧
    T (fun i => v (Sum.inl (Sum.inl i))) (fun j => v (Sum.inr j)) =
      (fun j => v (Sum.inl (Sum.inr j)))}

theorem regularCoefficientGraph_projectionFiber {ι κ : Type}
    (Ω : (ι → ℝ) → Set (κ → ℝ)) (T : (ι → ℝ) → (κ → ℝ) → (κ → ℝ))
    (p : ι → ℝ) (y : κ → ℝ) :
    projectionFiber (regularCoefficientGraph Ω T) (Sum.elim p y) =
      {x : κ → ℝ | x ∈ Ω p ∧ T p x = y} := rfl

/-- Uniformity over coefficient valuations and external parameters for one
fixed raw graph syntax. Regularity is checked pointwise on each selected
parameter slice, after N has already been chosen. -/
theorem published_raw_regularCoefficientFiber_uniform_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    {C ι κ : Type} [Fintype C] [Fintype ι] [Fintype κ]
    (φ : Language.ring.Formula (C ⊕ ((ι ⊕ κ) ⊕ κ))) :
    ∃ N : ℕ, ∀ (σ : C → ℝ)
      (Ω : (ι → ℝ) → Set (κ → ℝ)) (T : (ι → ℝ) → (κ → ℝ) → (κ → ℝ)),
      regularCoefficientGraph Ω T = {v | φ.Realize (Sum.elim σ v)} →
      ∀ (p : ι → ℝ) (y : κ → ℝ),
      (∀ x ∈ Ω p, ∃ L : (κ → ℝ) →L[ℝ] (κ → ℝ),
        HasFDerivAt (T p) L x ∧ L.det ≠ 0) →
      Finite {x : κ → ℝ | x ∈ Ω p ∧ T p x = y} ∧
        Nat.card {x : κ → ℝ | x ∈ Ω p ∧ T p x = y} ≤ N := by
  obtain ⟨N, hN⟩ := published_raw_formula_constant_uniform_bound hCells hHardt hQQE φ
  refine ⟨N, ?_⟩
  intro σ Ω T hGraph p y hreg
  apply finite_regularCoefficientFiber_of_det_ne_zero (T p) (Ω p) y hreg
  have hFiber : {x : κ → ℝ | x ∈ Ω p ∧ T p x = y} =
      {x : κ → ℝ | φ.Realize (Sum.elim σ (Sum.elim (Sum.elim p y) x))} := by
    rw [← regularCoefficientGraph_projectionFiber Ω T p y, hGraph]
    rfl
  rw [hFiber]
  exact (hN σ (Sum.elim p y)).1

/-- A fixed definable selected graph supplies one N before every external
parameter and output, without an assumed finite-fiber or dimension premise. -/
theorem published_definable_regularCoefficientFiber_uniform_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (Ω : (ι → ℝ) → Set (κ → ℝ)) (T : (ι → ℝ) → (κ → ℝ) → (κ → ℝ))
    (hGraph : (Set.univ : Set ℝ).Definable Language.ring (regularCoefficientGraph Ω T)) :
    ∃ N : ℕ, ∀ (p : ι → ℝ) (y : κ → ℝ),
      (∀ x ∈ Ω p, ∃ L : (κ → ℝ) →L[ℝ] (κ → ℝ),
        HasFDerivAt (T p) L x ∧ L.det ≠ 0) →
      Finite {x : κ → ℝ | x ∈ Ω p ∧ T p x = y} ∧
        Nat.card {x : κ → ℝ | x ∈ Ω p ∧ T p x = y} ≤ N := by
  obtain ⟨N, hN⟩ := published_definable_component_and_geometric_fiber_bound
    hCells hHardt hQQE (regularCoefficientGraph Ω T) hGraph
  refine ⟨N, ?_⟩
  intro p y hreg
  exact finite_regularCoefficientFiber_of_det_ne_zero (T p) (Ω p) y hreg
    (hN (Sum.elim p y)).1

/-- A positive lower bound on the absolute Jacobian gives precisely the
nonvanishing needed above. The lower bound can depend on the external parameter;
N still comes first, since it is supplied by the fixed joint graph format. -/
theorem published_regularCoefficientFiber_bound_of_jacobian_lower_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (Ω : (ι → ℝ) → Set (κ → ℝ)) (T : (ι → ℝ) → (κ → ℝ) → (κ → ℝ))
    (hGraph : (Set.univ : Set ℝ).Definable Language.ring (regularCoefficientGraph Ω T)) :
    ∃ N : ℕ, ∀ (p : ι → ℝ) (y : κ → ℝ) (δ : ℝ), 0 < δ →
      (∀ x ∈ Ω p, ∃ L : (κ → ℝ) →L[ℝ] (κ → ℝ),
        HasFDerivAt (T p) L x ∧ δ ≤ |L.det|) →
      Finite {x : κ → ℝ | x ∈ Ω p ∧ T p x = y} ∧
        Nat.card {x : κ → ℝ | x ∈ Ω p ∧ T p x = y} ≤ N := by
  obtain ⟨N, hN⟩ := published_definable_regularCoefficientFiber_uniform_bound
    hCells hHardt hQQE Ω T hGraph
  refine ⟨N, ?_⟩
  intro p y δ hδ hreg
  apply hN p y
  intro x hx
  obtain ⟨L, hL, hdet⟩ := hreg x hx
  exact ⟨L, hL, abs_pos.mp (hδ.trans_le hdet)⟩

end PaperI
