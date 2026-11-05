import PaperILean.RawFormulaPolynomialPrenex

#check @PaperI.forall_scalar_tuple
#print axioms PaperI.forall_scalar_tuple
#check @PaperI.exists_scalar_tuple
#print axioms PaperI.exists_scalar_tuple
#check @PaperI.realize_castLE_append_scalar
#print axioms PaperI.realize_castLE_append_scalar
#check @PaperI.isPrenex_exists_scalar_prefix
#print axioms PaperI.isPrenex_exists_scalar_prefix
#check @PaperI.rawBoundedFormula_exists_scalar_prenex
#print axioms PaperI.rawBoundedFormula_exists_scalar_prenex
#check @PaperI.rawFormula_exists_scalar_prenex
#print axioms PaperI.rawFormula_exists_scalar_prenex
#check @PaperI.scalar_prefix_variableCount_eq_length
#print axioms PaperI.scalar_prefix_variableCount_eq_length
#check @PaperI.rawFormula_prenex_polynomial_representation
#print axioms PaperI.rawFormula_prenex_polynomial_representation
#check @PaperI.RawFormulaPolynomialPrenexData
#print axioms PaperI.RawFormulaPolynomialPrenexData
#check @PaperI.compileRawFormulaToPolynomialPrenex
#print axioms PaperI.compileRawFormulaToPolynomialPrenex
#check @PaperI.compileRawFormulaToPolynomialPrenex_realize
#print axioms PaperI.compileRawFormulaToPolynomialPrenex_realize
#check @PaperI.compileRawFormulaToPolynomialPrenex_variableCount
#print axioms PaperI.compileRawFormulaToPolynomialPrenex_variableCount
#check @PaperI.RawFormulaPolynomialPrenexData.mk
#print axioms PaperI.RawFormulaPolynomialPrenexData.mk
#check @PaperI.RawFormulaPolynomialPrenexData.blocks
#print axioms PaperI.RawFormulaPolynomialPrenexData.blocks
#check @PaperI.RawFormulaPolynomialPrenexData.atomCount
#print axioms PaperI.RawFormulaPolynomialPrenexData.atomCount
#check @PaperI.RawFormulaPolynomialPrenexData.degreeBound
#print axioms PaperI.RawFormulaPolynomialPrenexData.degreeBound
#check @PaperI.RawFormulaPolynomialPrenexData.polynomial
#print axioms PaperI.RawFormulaPolynomialPrenexData.polynomial
#check @PaperI.RawFormulaPolynomialPrenexData.boolean
#print axioms PaperI.RawFormulaPolynomialPrenexData.boolean
#check @PaperI.RawFormulaPolynomialPrenexData.scalar_blocks
#print axioms PaperI.RawFormulaPolynomialPrenexData.scalar_blocks
#check @PaperI.RawFormulaPolynomialPrenexData.degree_le
#print axioms PaperI.RawFormulaPolynomialPrenexData.degree_le
#check @PaperI.RawFormulaPolynomialPrenexData.correct
#print axioms PaperI.RawFormulaPolynomialPrenexData.correct

namespace RawPrenex105Boundary
open FirstOrder PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def eqMatrix : Language.ring.BoundedFormula Empty 2 :=
  (Language.Term.var (Sum.inr 0)).bdEqual (Language.Term.var (Sum.inr 1))

-- The compiled positive order is true at the unique empty free valuation.
example : (fun x : Empty => x.elim : Empty → ℝ) ∈
    polynomialPrenexSet (compileRawFormulaToPolynomialPrenex eqMatrix.ex.all).blocks
      (compileRawFormulaToPolynomialPrenex eqMatrix.ex.all).polynomial
      (compileRawFormulaToPolynomialPrenex eqMatrix.ex.all).boolean := by
  apply (compileRawFormulaToPolynomialPrenex_realize _ _).mp
  simp [Language.Formula.Realize, eqMatrix, Language.BoundedFormula.realize_all,
    Language.BoundedFormula.realize_ex, Language.BoundedFormula.realize_bdEqual,
    Language.Term.realize, Fin.snoc]

-- Reversing the actual quantifiers remains false after compilation.
example : ¬ (fun x : Empty => x.elim : Empty → ℝ) ∈
    polynomialPrenexSet (compileRawFormulaToPolynomialPrenex eqMatrix.all.ex).blocks
      (compileRawFormulaToPolynomialPrenex eqMatrix.all.ex).polynomial
      (compileRawFormulaToPolynomialPrenex eqMatrix.all.ex).boolean := by
  intro h
  have hr := (compileRawFormulaToPolynomialPrenex_realize _ _).mpr h
  simp only [Language.Formula.Realize, eqMatrix, Language.BoundedFormula.realize_all,
    Language.BoundedFormula.realize_ex, Language.BoundedFormula.realize_bdEqual,
    Language.Term.realize, Sum.elim_inr] at hr
  obtain ⟨x, hx⟩ := hr
  have h0 := hx 0
  have h1 := hx 1
  norm_num [Fin.snoc] at h0 h1
  norm_num [h0] at h1

-- Negating the true quantified raw formula remains false after compilation.
example : ¬ (fun x : Empty => x.elim : Empty → ℝ) ∈
    polynomialPrenexSet (compileRawFormulaToPolynomialPrenex eqMatrix.ex.all.not).blocks
      (compileRawFormulaToPolynomialPrenex eqMatrix.ex.all.not).polynomial
      (compileRawFormulaToPolynomialPrenex eqMatrix.ex.all.not).boolean := by
  intro h
  have hr := (compileRawFormulaToPolynomialPrenex_realize _ _).mpr h
  simp [Language.Formula.Realize, eqMatrix, Language.BoundedFormula.realize_all,
    Language.BoundedFormula.realize_ex, Language.BoundedFormula.realize_not,
    Language.BoundedFormula.realize_bdEqual, Language.Term.realize, Fin.snoc] at hr
end RawPrenex105Boundary
