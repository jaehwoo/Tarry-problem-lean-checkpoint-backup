import PaperILean.RawPrenexRealization
import PaperILean.RingQuantifierFreeMatrix

/-! Compile an actual raw ring formula to the existing polynomial prenex
representation. All output syntax and degree bounds are chosen before every
real valuation, including any constant names represented by free variables.
The proof combines checked mathlib prenex normalization with the checked
polynomial compilation of the actual quantifier-free matrix. -/

noncomputable section
namespace PaperI
open FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem rawFormula_prenex_polynomial_representation {α : Type*}
    (φ : Language.ring.Formula α) :
    ∃ (blocks : QuantifierPrefix) (s D : ℕ),
      ∃ (p : Fin s → MvPolynomial (α ⊕ Fin (quantifierVariableCount blocks)) ℝ)
        (b : (Fin s → Bool × Bool) → Bool),
        (∀ block ∈ blocks, block.2 = 1) ∧
        (∀ i, (p i).totalDegree ≤ D) ∧
        {v | φ.Realize v} = polynomialPrenexSet blocks p b := by
  obtain ⟨blocks, hone, ψ, hq, hsem⟩ := rawFormula_exists_scalar_prenex φ
  obtain ⟨p, b, hp, hmatrix⟩ := ringQF_exists_polynomialBoolean_realize ψ hq
  refine ⟨blocks, ringFormulaAtomBound ψ, ringFormulaDegreeBound ψ, p, b, hone, hp, ?_⟩
  ext v
  refine (hsem v).trans ?_
  apply realizeQuantifierPrefix_congr
  intro ys
  exact hmatrix v ys

/-- A checked compilation certificate for one fixed raw formula. -/
structure RawFormulaPolynomialPrenexData {α : Type*} (φ : Language.ring.Formula α) where
  blocks : QuantifierPrefix
  atomCount : ℕ
  degreeBound : ℕ
  polynomial : Fin atomCount →
    MvPolynomial (α ⊕ Fin (quantifierVariableCount blocks)) ℝ
  boolean : (Fin atomCount → Bool × Bool) → Bool
  scalar_blocks : ∀ block ∈ blocks, block.2 = 1
  degree_le : ∀ i, (polynomial i).totalDegree ≤ degreeBound
  correct : {v | φ.Realize v} = polynomialPrenexSet blocks polynomial boolean

/-- Noncomputable selection of the proved certificate; this is not an
unchecked evaluator or an asserted external compiler specification. -/
def compileRawFormulaToPolynomialPrenex {α : Type*} (φ : Language.ring.Formula α) :
    RawFormulaPolynomialPrenexData φ :=
  Classical.choice (by
    obtain ⟨blocks, s, D, p, b, hone, hp, hEq⟩ :=
      rawFormula_prenex_polynomial_representation φ
    exact ⟨⟨blocks, s, D, p, b, hone, hp, hEq⟩⟩)

theorem compileRawFormulaToPolynomialPrenex_realize {α : Type*}
    (φ : Language.ring.Formula α) (v : α → ℝ) :
    φ.Realize v ↔
      v ∈ polynomialPrenexSet (compileRawFormulaToPolynomialPrenex φ).blocks
        (compileRawFormulaToPolynomialPrenex φ).polynomial
        (compileRawFormulaToPolynomialPrenex φ).boolean :=
  Set.ext_iff.mp (compileRawFormulaToPolynomialPrenex φ).correct v

theorem compileRawFormulaToPolynomialPrenex_variableCount {α : Type*}
    (φ : Language.ring.Formula α) :
    quantifierVariableCount (compileRawFormulaToPolynomialPrenex φ).blocks =
      (compileRawFormulaToPolynomialPrenex φ).blocks.length :=
  scalar_prefix_variableCount_eq_length _ (compileRawFormulaToPolynomialPrenex φ).scalar_blocks

end PaperI
