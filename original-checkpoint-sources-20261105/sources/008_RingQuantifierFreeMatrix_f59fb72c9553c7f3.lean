import PaperILean.RingTermPolynomial
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple
import Mathlib.ModelTheory.Complexity

/-! Exact raw ring quantifier-free formulas as polynomial Boolean matrices.
The extracted atom and degree budgets are functions of syntax, before every
real valuation. Arbitrary named real constants are represented by additional
free-variable slots and keep their actual real valuations. The semantic claim
requires mathlib's `IsQF`; the polynomial extractor's `all` branch is unused by
that claim. No order atom or quantified square witness is silently treated as
quantifier-free, and no external compiler assumption is used. -/

noncomputable section
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Number of equality-atom occurrences in the actual raw ring syntax. -/
def ringFormulaAtomBound {α : Type*} :
    {n : ℕ} → Language.ring.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 1
  | _, .rel r _ => nomatch r
  | _, .imp φ ψ => ringFormulaAtomBound φ + ringFormulaAtomBound ψ
  | _, .all φ => ringFormulaAtomBound φ

/-- Syntactic degree budget of the difference polynomials in all equality atoms. -/
def ringFormulaDegreeBound {α : Type*} :
    {n : ℕ} → Language.ring.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal t u => max (ringTermDegreeBound t) (ringTermDegreeBound u)
  | _, .rel r _ => nomatch r
  | _, .imp φ ψ => max (ringFormulaDegreeBound φ) (ringFormulaDegreeBound ψ)
  | _, .all φ => ringFormulaDegreeBound φ

/-- Actual difference polynomials of a quantifier-free matrix. No semantics is
claimed for the deliberately unused universal-quantifier branch. -/
def ringQFPolynomialFamily {α : Type*} :
    {n : ℕ} → Language.ring.BoundedFormula α n → Finset (MvPolynomial (α ⊕ Fin n) ℝ)
  | _, .falsum => ∅
  | _, .equal t u => {ringTermPolynomial t - ringTermPolynomial u}
  | _, .rel r _ => nomatch r
  | _, .imp φ ψ => ringQFPolynomialFamily φ ∪ ringQFPolynomialFamily ψ
  | _, .all _ => ∅

/-- Flatten only the coordinate labels, retaining the exact free/bound split
used by `BoundedFormula.Realize`. -/
def ringBoundedFormulaSet {α : Type*} {n : ℕ}
    (φ : Language.ring.BoundedFormula α n) : Set ((α ⊕ Fin n) → ℝ) :=
  {x | φ.Realize (fun a => x (Sum.inl a)) (fun i => x (Sum.inr i))}

theorem ringQFPolynomialFamily_card_le {α : Type*} {n : ℕ}
    (φ : Language.ring.BoundedFormula α n) :
    (ringQFPolynomialFamily φ).card ≤ ringFormulaAtomBound φ := by
  induction φ with
  | falsum => simp [ringQFPolynomialFamily, ringFormulaAtomBound]
  | equal t u => simp [ringQFPolynomialFamily, ringFormulaAtomBound]
  | rel r _ => exact r.elim
  | imp φ ψ ihφ ihψ =>
    exact Finset.card_union_le.trans (Nat.add_le_add ihφ ihψ)
  | all φ _ => simp [ringQFPolynomialFamily]

theorem ringQFPolynomialFamily_totalDegree_le {α : Type*} {n : ℕ}
    (φ : Language.ring.BoundedFormula α n) :
    ∀ p ∈ ringQFPolynomialFamily φ, p.totalDegree ≤ ringFormulaDegreeBound φ := by
  induction φ with
  | falsum => simp [ringQFPolynomialFamily]
  | equal t u =>
    intro p hp
    have heq := Finset.mem_singleton.mp hp
    subst p
    exact ringTermPolynomial_sub_totalDegree_le t u
  | rel r _ => exact r.elim
  | imp φ ψ ihφ ihψ =>
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (ihφ p hp).trans (Nat.le_max_left _ _)
    · exact (ihψ p hp).trans (Nat.le_max_right _ _)
  | all φ _ => simp [ringQFPolynomialFamily]

/-- Raw QF truth is determined by signs of the compiled atoms, proved by
induction over mathlib's actual quantifier-free-formula predicate. -/
theorem ringQFPolynomialFamily_signDetermined {α : Type*} {n : ℕ}
    (φ : Language.ring.BoundedFormula α n) (hφ : φ.IsQF) :
    PolynomialSignDetermined (ringQFPolynomialFamily φ) (ringBoundedFormulaSet φ) := by
  induction hφ with
  | falsum =>
    intro x y _
    rfl
  | of_isAtomic h =>
    cases h with
    | equal t u =>
      intro x y hxy
      have hz := (hxy _ (Finset.mem_singleton_self _)).1
      rw [ringTermPolynomial_sub_eq_zero_iff, ringTermPolynomial_sub_eq_zero_iff] at hz
      simpa [ringBoundedFormulaSet, Language.BoundedFormula.Realize,
        Language.Term.bdEqual, Sum.elim_comp_inl_inr] using hz
    | rel r _ => exact r.elim
  | @imp φ ψ hφ hψ ihφ ihψ =>
    intro x y hxy
    exact imp_congr
      (ihφ x y (fun p hp => hxy p (Finset.mem_union_left _ hp)))
      (ihψ x y (fun p hp => hxy p (Finset.mem_union_right _ hp)))

/-- The actual raw QF formula has a polynomial-sign Boolean matrix, with the
atom count and degree fixed syntactically before all real assignments. -/
theorem ringQF_exists_polynomialBooleanSet {α : Type*} {n : ℕ}
    (φ : Language.ring.BoundedFormula α n) (hφ : φ.IsQF) :
    ∃ (p : Fin (ringFormulaAtomBound φ) → MvPolynomial (α ⊕ Fin n) ℝ)
      (b : (Fin (ringFormulaAtomBound φ) → Bool × Bool) → Bool),
      (∀ i, (p i).totalDegree ≤ ringFormulaDegreeBound φ) ∧
      ringBoundedFormulaSet φ = polynomialBooleanSet p b := by
  obtain ⟨p, hp, hsign⟩ := exists_bounded_polynomial_tuple_of_signDetermined
    (ringQFPolynomialFamily φ) (ringBoundedFormulaSet φ)
    (ringFormulaAtomBound φ) (ringFormulaDegreeBound φ)
    (ringQFPolynomialFamily_card_le φ) (ringQFPolynomialFamily_totalDegree_le φ)
    (ringQFPolynomialFamily_signDetermined φ hφ)
  obtain ⟨b, hb⟩ := polynomialSignDetermined_exists_boolean_table p _ hsign
  exact ⟨p, b, hp, hb⟩

/-- Pointwise form for the prenex compiler: every occurrence uses the same
free assignment and the same complete tuple of bound coordinates. -/
theorem ringQF_exists_polynomialBoolean_realize {α : Type*} {n : ℕ}
    (φ : Language.ring.BoundedFormula α n) (hφ : φ.IsQF) :
    ∃ (p : Fin (ringFormulaAtomBound φ) → MvPolynomial (α ⊕ Fin n) ℝ)
      (b : (Fin (ringFormulaAtomBound φ) → Bool × Bool) → Bool),
      (∀ i, (p i).totalDegree ≤ ringFormulaDegreeBound φ) ∧
      ∀ (v : α → ℝ) (xs : Fin n → ℝ),
        φ.Realize v xs ↔ Sum.elim v xs ∈ polynomialBooleanSet p b := by
  obtain ⟨p, b, hp, hEq⟩ := ringQF_exists_polynomialBooleanSet φ hφ
  refine ⟨p, b, hp, ?_⟩
  intro v xs
  have h := Set.ext_iff.mp hEq (Sum.elim v xs)
  simpa [ringBoundedFormulaSet] using h

end PaperI
