import PaperILean.RegularCoefficientFiberBounds
import PaperILean.RealPolynomialDefinability
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Concrete polynomial-map application of I665. Every input/output/external
coordinate is retained. Graph definability is proved from the actual polynomial
tuple and the joint selected domain; it is not an extra graph or cardinality
assumption. The tuple is fixed before N, and N precedes all external parameter
and output values. No uniformity across unbounded changing polynomial degrees
is claimed. Pre-strategy: checkpoint 106 regular-polynomial diagnostic. -/

noncomputable section
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def regularPolynomialMap {ι κ : Type}
    (q : κ → MvPolynomial (ι ⊕ κ) ℝ) (p : ι → ℝ) (x : κ → ℝ) : κ → ℝ :=
  fun j => MvPolynomial.eval (Sum.elim p x) (q j)

def regularPolynomialGraphEquation {ι κ : Type}
    (q : κ → MvPolynomial (ι ⊕ κ) ℝ) (j : κ) :
    MvPolynomial ((ι ⊕ κ) ⊕ κ) ℝ :=
  MvPolynomial.rename (Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr) (q j) -
    MvPolynomial.X (Sum.inl (Sum.inr j))

theorem eval_regularPolynomialGraphEquation {ι κ : Type}
    (q : κ → MvPolynomial (ι ⊕ κ) ℝ) (j : κ) (v : ((ι ⊕ κ) ⊕ κ) → ℝ) :
    MvPolynomial.eval v (regularPolynomialGraphEquation q j) =
      regularPolynomialMap q (fun i => v (Sum.inl (Sum.inl i)))
        (fun i => v (Sum.inr i)) j - v (Sum.inl (Sum.inr j)) := by
  rw [regularPolynomialGraphEquation, map_sub, MvPolynomial.eval_X,
    MvPolynomial.eval_rename]
  have he : v ∘ Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr =
      Sum.elim (fun i => v (Sum.inl (Sum.inl i))) (fun i => v (Sum.inr i)) := by
    funext a
    cases a <;> rfl
  rw [he]
  rfl

/-- Actual polynomial evaluation gives a definable joint graph over the
selected joint domain, including the empty-coordinate and empty-domain cases. -/
theorem regularPolynomialMap_graph_definable {ι κ : Type} [Fintype κ]
    (q : κ → MvPolynomial (ι ⊕ κ) ℝ) (U : Set ((ι ⊕ κ) → ℝ))
    (hU : (Set.univ : Set ℝ).Definable Language.ring U) :
    (Set.univ : Set ℝ).Definable Language.ring
      (regularCoefficientGraph (projectionFiber U) (regularPolynomialMap q)) := by
  classical
  let e : (ι ⊕ κ) → ((ι ⊕ κ) ⊕ κ) :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr
  have hDom := hU.preimage_comp e
  have hEq : (Set.univ : Set ℝ).Definable Language.ring
      {v : ((ι ⊕ κ) ⊕ κ) → ℝ |
        ∀ j, MvPolynomial.eval v (regularPolynomialGraphEquation q j) = 0} := by
    have h := Set.definable_finset_biInter
      (fun j => realPolynomial_zero_definable (regularPolynomialGraphEquation q j)) Finset.univ
    convert h using 1
    ext v
    simp
  convert hDom.inter hEq using 1
  ext v
  have he : v ∘ e =
      Sum.elim (fun i => v (Sum.inl (Sum.inl i))) (fun i => v (Sum.inr i)) := by
    funext a
    cases a <;> rfl
  simp only [regularCoefficientGraph, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_preimage, he, projectionFiber]
  congr 1
  simp only [funext_iff, eval_regularPolynomialGraphEquation, sub_eq_zero]

/-- Concrete polynomial selected branches have uniformly finite regular fibers.
The derivative and determinant are those of the actual polynomial slice. -/
theorem published_regularPolynomialFiber_uniform_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (q : κ → MvPolynomial (ι ⊕ κ) ℝ) (U : Set ((ι ⊕ κ) → ℝ))
    (hU : (Set.univ : Set ℝ).Definable Language.ring U) :
    ∃ N : ℕ, ∀ (p : ι → ℝ) (y : κ → ℝ) (δ : ℝ), 0 < δ →
      (∀ x, Sum.elim p x ∈ U → ∃ L : (κ → ℝ) →L[ℝ] (κ → ℝ),
        HasFDerivAt (regularPolynomialMap q p) L x ∧ δ ≤ |L.det|) →
      Finite {x : κ → ℝ | Sum.elim p x ∈ U ∧ regularPolynomialMap q p x = y} ∧
        Nat.card {x : κ → ℝ | Sum.elim p x ∈ U ∧ regularPolynomialMap q p x = y} ≤ N :=
  published_regularCoefficientFiber_bound_of_jacobian_lower_bound hCells hHardt hQQE
    (projectionFiber U) (regularPolynomialMap q) (regularPolynomialMap_graph_definable q U hU)

/-- Polynomial slices are actually differentiable; no separate smoothness
premise is needed in the determinant application below. -/
theorem differentiable_regularPolynomialMap {ι κ : Type} [Fintype κ]
    (q : κ → MvPolynomial (ι ⊕ κ) ℝ) (p : ι → ℝ) :
    Differentiable ℝ (regularPolynomialMap q p) := by
  have hs : ∀ Q : MvPolynomial (ι ⊕ κ) ℝ,
      Differentiable ℝ (fun x : κ → ℝ => MvPolynomial.eval (Sum.elim p x) Q) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C a => simpa using (differentiable_const (a : ℝ) :
        Differentiable ℝ (fun _ : κ → ℝ => a))
    | add Q R hQ hR => simpa using hQ.add hR
    | mul_X Q j hQ =>
      cases j with
      | inl i => simpa using hQ.mul (differentiable_const (p i))
      | inr j => simpa using hQ.mul (differentiable_apply j)
  apply differentiable_pi.mpr
  intro j
  exact hs (q j)

/-- The final polynomial instance assumes only the actual Jacobian lower
bound on the selected domain; its derivative existence is proved locally. -/
theorem published_regularPolynomialFiber_bound_of_jacobian_lower_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (q : κ → MvPolynomial (ι ⊕ κ) ℝ) (U : Set ((ι ⊕ κ) → ℝ))
    (hU : (Set.univ : Set ℝ).Definable Language.ring U) :
    ∃ N : ℕ, ∀ (p : ι → ℝ) (y : κ → ℝ) (δ : ℝ), 0 < δ →
      (∀ x, Sum.elim p x ∈ U →
        δ ≤ |(fderiv ℝ (regularPolynomialMap q p) x).det|) →
      Finite {x : κ → ℝ | Sum.elim p x ∈ U ∧ regularPolynomialMap q p x = y} ∧
        Nat.card {x : κ → ℝ | Sum.elim p x ∈ U ∧ regularPolynomialMap q p x = y} ≤ N := by
  obtain ⟨N, hN⟩ := published_regularPolynomialFiber_uniform_bound hCells hHardt hQQE q U hU
  refine ⟨N, ?_⟩
  intro p y δ hδ hdet
  apply hN p y δ hδ
  intro x hx
  exact ⟨fderiv ℝ (regularPolynomialMap q p) x,
    (differentiable_regularPolynomialMap q p x).hasFDerivAt, hdet x hx⟩

end PaperI
