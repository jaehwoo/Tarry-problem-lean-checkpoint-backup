import PaperILean.UniversalSignFamily
import Mathlib.Data.Fin.Tuple.Basic

/-! Exact prenex polynomial-sign syntax for BPR's `(P, Pi)` formulas.
A prefix is an ordered list of vector blocks. `true` denotes universal and
`false` existential quantification; adjacent equal quantifiers, zero-size
blocks, and the empty prefix are allowed. The free coordinates and all bound
coordinates are disjoint. The matrix is an arbitrary finite Boolean table on
polynomial signs, reusing the checked checkpoint-103 encoding.

This is an explicit prenex representation, not a claimed complexity-preserving
compiler from every mathlib first-order formula. In particular, the existing
ring-language encoding of order using squares must not be assigned this
ordered-polynomial format without a separate translation argument.
Executed obstruction checks: checkpoint_104_quantified_format_pre_strategy.json. -/

noncomputable section
namespace PaperI

abbrev QuantifierPrefix := List (Bool × ℕ)

/-- Total number of quantified scalar real coordinates, including every block. -/
def quantifierVariableCount : QuantifierPrefix → ℕ
  | [] => 0
  | block :: tail => block.2 + quantifierVariableCount tail

/-- Interpret blocks in the written outer-to-inner order, with one common
assignment for every occurrence of a bound variable in the matrix. -/
def realizeQuantifierPrefix : (prefix : QuantifierPrefix) →
    ((Fin (quantifierVariableCount prefix) → ℝ) → Prop) → Prop
  | [], matrix => matrix Fin.elim0
  | (kind, size) :: tail, matrix =>
    if kind then
      ∀ x : Fin size → ℝ,
        realizeQuantifierPrefix tail (fun y => matrix (Fin.append x y))
    else
      ∃ x : Fin size → ℝ,
        realizeQuantifierPrefix tail (fun y => matrix (Fin.append x y))

/-- A quantified polynomial formula's exact realization in its free coordinates. -/
def polynomialPrenexSet {α : Type*} {s : ℕ} (prefix : QuantifierPrefix)
    (p : Fin s → MvPolynomial (α ⊕ Fin (quantifierVariableCount prefix)) ℝ)
    (b : (Fin s → Bool × Bool) → Bool) : Set (α → ℝ) :=
  {x | realizeQuantifierPrefix prefix
    (fun y => Sum.elim x y ∈ polynomialBooleanSet p b)}

@[simp] theorem realizeQuantifierPrefix_nil (matrix : (Fin 0 → ℝ) → Prop) :
    realizeQuantifierPrefix [] matrix ↔ matrix Fin.elim0 := Iff.rfl

@[simp] theorem realizeQuantifierPrefix_forall (size : ℕ) (tail : QuantifierPrefix)
    (matrix : (Fin (size + quantifierVariableCount tail) → ℝ) → Prop) :
    realizeQuantifierPrefix ((true, size) :: tail) matrix ↔
      ∀ x : Fin size → ℝ,
        realizeQuantifierPrefix tail (fun y => matrix (Fin.append x y)) := Iff.rfl

@[simp] theorem realizeQuantifierPrefix_exists (size : ℕ) (tail : QuantifierPrefix)
    (matrix : (Fin (size + quantifierVariableCount tail) → ℝ) → Prop) :
    realizeQuantifierPrefix ((false, size) :: tail) matrix ↔
      ∃ x : Fin size → ℝ,
        realizeQuantifierPrefix tail (fun y => matrix (Fin.append x y)) := Iff.rfl

/-- Matrix equivalence preserves the entire prefix, including quantifier order. -/
theorem realizeQuantifierPrefix_congr (prefix : QuantifierPrefix)
    (matrix matrix' : (Fin (quantifierVariableCount prefix) → ℝ) → Prop)
    (h : ∀ x, matrix x ↔ matrix' x) :
    realizeQuantifierPrefix prefix matrix ↔ realizeQuantifierPrefix prefix matrix' := by
  induction prefix with
  | nil => exact h Fin.elim0
  | cons block tail ih =>
    rcases block with ⟨kind, size⟩
    cases kind
    · exact exists_congr (fun x => ih _ _ (fun y => h (Fin.append x y)))
    · exact forall_congr' (fun x => ih _ _ (fun y => h (Fin.append x y)))

/-- Empty quantified blocks are genuine identities because there is exactly one
empty assignment. Both quantifiers have the same identity behavior. -/
theorem realizeQuantifierPrefix_zero_block (kind : Bool) (tail : QuantifierPrefix)
    (matrix : (Fin (quantifierVariableCount tail) → ℝ) → Prop) :
    realizeQuantifierPrefix ((kind, 0) :: tail)
      (fun x => matrix (fun i => x (Fin.cast (Nat.zero_add _).symm i))) ↔
      realizeQuantifierPrefix tail matrix := by
  have h (x : Fin 0 → ℝ) :
      (fun y : Fin (quantifierVariableCount tail) → ℝ =>
        matrix (fun i => Fin.append x y (Fin.cast (Nat.zero_add _).symm i))) = matrix := by
    funext y
    congr 1
    funext i
    simp [Fin.append_left_nil]
  cases kind <;> simp only [realizeQuantifierPrefix, Bool.false_eq_true, ↓reduceIte,
    h, Bool.true_eq_true, forall_const, exists_const]

/-- Quantification of a constant truth value preserves it; all finite real
vector spaces, including the zero-coordinate space, have an assignment. -/
theorem realizeQuantifierPrefix_const (prefix : QuantifierPrefix) (r : Prop) :
    realizeQuantifierPrefix prefix (fun _ => r) ↔ r := by
  induction prefix with
  | nil => rfl
  | cons block tail ih =>
    rcases block with ⟨kind, size⟩
    cases kind <;> simp [realizeQuantifierPrefix, ih]

/-- A different Boolean presentation of the same matrix does not alter the
quantified set, with its original free-coordinate scope retained. -/
theorem polynomialPrenexSet_congr_matrix {α : Type*} {s t : ℕ}
    (prefix : QuantifierPrefix)
    (p : Fin s → MvPolynomial (α ⊕ Fin (quantifierVariableCount prefix)) ℝ)
    (b : (Fin s → Bool × Bool) → Bool)
    (q : Fin t → MvPolynomial (α ⊕ Fin (quantifierVariableCount prefix)) ℝ)
    (c : (Fin t → Bool × Bool) → Bool)
    (h : polynomialBooleanSet p b = polynomialBooleanSet q c) :
    polynomialPrenexSet prefix p b = polynomialPrenexSet prefix q c := by
  ext x
  apply realizeQuantifierPrefix_congr
  intro y
  rw [h]

@[simp] theorem polynomialPrenexSet_true {α : Type*} {s : ℕ}
    (prefix : QuantifierPrefix)
    (p : Fin s → MvPolynomial (α ⊕ Fin (quantifierVariableCount prefix)) ℝ) :
    polynomialPrenexSet prefix p (fun _ => true) = Set.univ := by
  ext x
  simp [polynomialPrenexSet, polynomialBooleanSet, realizeQuantifierPrefix_const]

@[simp] theorem polynomialPrenexSet_false {α : Type*} {s : ℕ}
    (prefix : QuantifierPrefix)
    (p : Fin s → MvPolynomial (α ⊕ Fin (quantifierVariableCount prefix)) ℝ) :
    polynomialPrenexSet prefix p (fun _ => false) = ∅ := by
  ext x
  simp [polynomialPrenexSet, polynomialBooleanSet, realizeQuantifierPrefix_const]

end PaperI
