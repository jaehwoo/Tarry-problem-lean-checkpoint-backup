import PaperILean.QuantifiedPolynomialFormat
import Mathlib.ModelTheory.Complexity

open FirstOrder
namespace Prenex105Diagnostics
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

-- Quantifier order must be preserved: the common-witness orders differ.
example : ∀ x : ℝ, ∃ y : ℝ, x = y := fun x => ⟨x, rfl⟩
example : ¬ (∃ x : ℝ, ∀ y : ℝ, x = y) := by
  rintro ⟨x, h⟩
  have h0 := h 0
  have h1 := h 1
  norm_num [h0] at h1

-- Separate witnesses for separate atoms cannot replace one common assignment.
example : (∃ x : ℝ, x = 0) ∧ (∃ x : ℝ, x = 1) := ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
example : ¬ ∃ x : ℝ, x = 0 ∧ x = 1 := by
  rintro ⟨x, h0, h1⟩
  norm_num [h0] at h1

-- Existing bound variables precede newly quantified ones under snoc.
example : (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → ℝ) 3) 7 : Fin 2 → ℝ) 0 = 3 := by
  norm_num [Fin.snoc]
example : (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → ℝ) 3) 7 : Fin 2 → ℝ) 1 = 7 := by
  norm_num [Fin.snoc]
example (n m : ℕ) (xs : Fin n → ℝ) (a : ℝ) (ys : Fin m → ℝ) :
    Fin.append (Fin.snoc xs a) ys =
      Fin.append xs (Fin.cons a ys) ∘ Fin.cast (Nat.succ_add_eq_add_succ ..) :=
  Fin.append_left_snoc xs a ys

-- Free and bound variables are different constructors and use different valuations.
example (v : Unit → ℝ) (xs : Fin 1 → ℝ) :
    (Language.Term.var (Sum.inl ()) : Language.ring.Term (Unit ⊕ Fin 1)).realize
      (Sum.elim v xs) = v () := rfl
example (v : Unit → ℝ) (xs : Fin 1 → ℝ) :
    (Language.Term.var (Sum.inr 0) : Language.ring.Term (Unit ⊕ Fin 1)).realize
      (Sum.elim v xs) = xs 0 := rfl

-- Negation changes both the truth condition and quantifier kind.
example (P : ℝ → Prop) : (¬ ∀ x, P x) ↔ ∃ x, ¬ P x := not_forall
example (P : ℝ → Prop) : (¬ ∃ x, P x) ↔ ∀ x, ¬ P x := not_exists

-- The empty prefix and a zero-variable context retain their unique assignment.
example (M : (Fin 0 → ℝ) → Prop) : PaperI.realizeQuantifierPrefix [] M ↔ M Fin.elim0 := Iff.rfl
example (xs : Fin 0 → ℝ) : xs = Fin.elim0 := Subsingleton.elim _ _

-- The actual raw bounded formula stores outer x at0 and inner y at1.
def matrix : Language.ring.BoundedFormula Empty 2 :=
  (Language.Term.var (Sum.inr 0)).bdEqual (Language.Term.var (Sum.inr 1))
example : matrix.ex.all.Realize (fun x : Empty => x.elim : Empty → ℝ) Fin.elim0 := by
  simp [matrix, Language.BoundedFormula.realize_all, Language.BoundedFormula.realize_ex,
    Language.BoundedFormula.realize_bdEqual, Language.Term.realize, Fin.snoc]
end Prenex105Diagnostics
