import PaperILean.PublishedQuantifiedConditioning
import PaperILean.RealPolynomialDefinability
noncomputable section
open FirstOrder
namespace PaperI.RawUniform105Pretest
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def coefficientZero : Language.ring.Formula (Unit ⊕ Unit) :=
  .equal (Language.Term.var (Sum.inl (Sum.inl ())) *
    Language.Term.var (Sum.inl (Sum.inr ()))) 0

def coefficientOne : Language.ring.Formula (Unit ⊕ Unit) :=
  .equal (Language.Term.var (Sum.inl (Sum.inl ())) *
    Language.Term.var (Sum.inl (Sum.inr ()))) 1

example (a x : ℝ) : coefficientZero.Realize (Sum.elim (fun _ => a) (fun _ => x)) ↔
    a * x = 0 := by
  simp [coefficientZero, Language.Formula.Realize, Language.BoundedFormula.Realize]

example (x : ℝ) : coefficientZero.Realize (Sum.elim (fun _ => 0) (fun _ => x)) := by
  simp [coefficientZero, Language.Formula.Realize, Language.BoundedFormula.Realize]

example (x : ℝ) : coefficientZero.Realize (Sum.elim (fun _ => 1) (fun _ => x)) ↔ x = 0 := by
  simp [coefficientZero, Language.Formula.Realize, Language.BoundedFormula.Realize]

example (x : ℝ) : ¬ coefficientOne.Realize (Sum.elim (fun _ => 0) (fun _ => x)) := by
  simp [coefficientOne, Language.Formula.Realize, Language.BoundedFormula.Realize]

-- Arbitrarily large real coefficients use the same fixed syntax.
example (a : ℝ) (ha : a ≠ 0) :
    coefficientOne.Realize (Sum.elim (fun _ => a) (fun _ => a⁻¹)) := by
  simpa [coefficientOne, Language.Formula.Realize, Language.BoundedFormula.Realize] using
    mul_inv_cancel₀ ha

def squareExists : Language.ring.Formula Unit :=
  (Language.BoundedFormula.equal
    (Language.Term.var (Sum.inr (0 : Fin 1)) * Language.Term.var (Sum.inr (0 : Fin 1)))
    (Language.Term.var (Sum.inl ()))).ex

example (x : ℝ) : squareExists.Realize (fun _ => x) ↔ 0 ≤ x := by
  change (Language.BoundedFormula.equal
    (Language.Term.var (Sum.inr (0 : Fin 1)) * Language.Term.var (Sum.inr (0 : Fin 1)))
    (Language.Term.var (Sum.inl ()))).ex.Realize (fun _ => x) default ↔ _
  rw [Language.BoundedFormula.realize_ex]
  simp only [Language.BoundedFormula.Realize, FirstOrder.Ring.realize_mul,
    Language.Term.realize_var, Sum.elim_inr, Sum.elim_inl, Fin.snoc_last]
  constructor
  · rintro ⟨y, rfl⟩
    exact mul_self_nonneg y
  · intro hx
    exact ⟨Real.sqrt x, Real.mul_self_sqrt hx⟩

-- Empty fiber remains compatible with an a priori common component bound.
example (N : ℕ) : Finite (ConnectedComponents (∅ : Set ℝ)) ∧
    Nat.card (ConnectedComponents (∅ : Set ℝ)) ≤ N := by
  constructor
  · infer_instance
  · simp
end PaperI.RawUniform105Pretest
