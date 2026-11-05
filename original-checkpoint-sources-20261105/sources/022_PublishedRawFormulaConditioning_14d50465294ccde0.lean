import PaperILean.QuantitativeQEImpliesQualitative
import PaperILean.PublishedQuantifiedConditioning

/-! Apply the checked raw-formula compiler to conditioning (ii), I623/I633/I638.
One fixed ring formula is compiled before any valuation. Named real constants
can be exposed as free coordinates; the same bound then precedes every value
of those constants and every external parameter. No coefficient magnitude
bound or assumed format certificate is used. Changing the formula syntax is
outside this fixed-formula theorem. Pre-strategy: checkpoint 105 record 015. -/

noncomputable section
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- The actual relation defined by fixed raw syntax has uniform fiber bounds.
The raw compiler is a theorem, not an extra input. -/
theorem published_raw_formula_component_and_geometric_fiber_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (φ : Language.ring.Formula (ι ⊕ κ)) :
    ∃ N : ℕ, ∀ p : ι → ℝ,
      (Finite (ConnectedComponents (projectionFiber {v | φ.Realize v} p)) ∧
        Nat.card (ConnectedComponents (projectionFiber {v | φ.Realize v} p)) ≤ N) ∧
      ∀ z : ℤ, HasGeometricSemialgebraicDimension
        (projectionFiber {v | φ.Realize v} p) z → z ≤ 0 →
        Finite (projectionFiber {v | φ.Realize v} p) ∧
          Nat.card (projectionFiber {v | φ.Realize v} p) ≤ N := by
  obtain ⟨blocks, s, D, q, b, _, hq, hEq⟩ :=
    rawFormula_prenex_polynomial_representation φ
  obtain ⟨N, hN⟩ := published_bounded_quantified_component_and_geometric_fiber_bound
    hCells hHardt hQQE.toRealSemialgebraicity hQQE ι κ
    blocks.length (quantifierVariableCount blocks) s D
  refine ⟨N, ?_⟩
  intro p
  rw [hEq]
  exact hN blocks le_rfl le_rfl s le_rfl q hq b p

/-- Constant names remain uniformly valued parameters of one fixed syntax.
No bound on their real magnitudes is required. -/
theorem published_raw_formula_constant_uniform_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    {C ι κ : Type} [Fintype C] [Fintype ι] [Fintype κ]
    (φ : Language.ring.Formula (C ⊕ (ι ⊕ κ))) :
    ∃ N : ℕ, ∀ (σ : C → ℝ) (p : ι → ℝ),
      (Finite (ConnectedComponents {x : κ → ℝ | φ.Realize (Sum.elim σ (Sum.elim p x))}) ∧
        Nat.card (ConnectedComponents {x : κ → ℝ |
          φ.Realize (Sum.elim σ (Sum.elim p x))}) ≤ N) ∧
      ∀ z : ℤ, HasGeometricSemialgebraicDimension
        {x : κ → ℝ | φ.Realize (Sum.elim σ (Sum.elim p x))} z → z ≤ 0 →
        Finite {x : κ → ℝ | φ.Realize (Sum.elim σ (Sum.elim p x))} ∧
          Nat.card {x : κ → ℝ | φ.Realize (Sum.elim σ (Sum.elim p x))} ≤ N := by
  let ψ : Language.ring.Formula ((C ⊕ ι) ⊕ κ) :=
    φ.relabel (Equiv.sumAssoc C ι κ).symm
  obtain ⟨N, hN⟩ := published_raw_formula_component_and_geometric_fiber_bound
    hCells hHardt hQQE ψ
  refine ⟨N, ?_⟩
  intro σ p
  have hFiber : projectionFiber {v | ψ.Realize v} (Sum.elim σ p) =
      {x : κ → ℝ | φ.Realize (Sum.elim σ (Sum.elim p x))} := by
    ext x
    change ψ.Realize (Sum.elim (Sum.elim σ p) x) ↔ _
    rw [show ψ = φ.relabel (Equiv.sumAssoc C ι κ).symm from rfl,
      Language.Formula.realize_relabel]
    congr 1
    funext a
    rcases a with c | (i | k) <;> rfl
  simpa only [hFiber] using hN (Sum.elim σ p)

/-- A definable relation has a fixed finite-constant raw presentation, so the
compiler applies to its actual fibers. This does not assert uniformity over
all definable relations of unbounded syntax. -/
theorem published_definable_component_and_geometric_fiber_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    {ι κ : Type} [Finite ι] [Finite κ]
    (S : Set ((ι ⊕ κ) → ℝ))
    (hS : (Set.univ : Set ℝ).Definable Language.ring S) :
    ∃ N : ℕ, ∀ p : ι → ℝ,
      (Finite (ConnectedComponents (projectionFiber S p)) ∧
        Nat.card (ConnectedComponents (projectionFiber S p)) ≤ N) ∧
      ∀ z : ℤ, HasGeometricSemialgebraicDimension (projectionFiber S p) z → z ≤ 0 →
        Finite (projectionFiber S p) ∧ Nat.card (projectionFiber S p) ≤ N := by
  classical
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite κ
  obtain ⟨C, _, hC⟩ := Set.definable_iff_finitely_definable.mp hS
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hC
  obtain ⟨N, hN⟩ := published_raw_formula_constant_uniform_bound hCells hHardt hQQE φ
  refine ⟨N, ?_⟩
  intro p
  rw [hφ]
  exact hN (fun c => c.val) p

end PaperI
