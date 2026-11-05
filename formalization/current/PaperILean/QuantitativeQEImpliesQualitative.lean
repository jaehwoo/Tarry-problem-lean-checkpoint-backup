import PaperILean.RawFormulaPolynomialPrenex
import PaperILean.PublishedQuantitativeQE
import PaperILean.PublishedGeometricFiberBounds

/-! I623/I626/I638: quantitative QE supplies the existing qualitative input.
The raw ring formula is compiled locally before the accepted quantitative QE
theorem is applied. Named real constants are first represented by a finite
set of free slots and then specialized by the checked polynomial fiber map.
No new external input or inhabitant of a published contract is introduced.
Pre-strategy diagnostics: checkpoint_105_qualitative_bridge_pre_strategy.json.
-/

noncomputable section
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- All finite-coordinate raw ring formulas admit a finite polynomial sign
description using only the accepted quantitative QE input. -/
theorem published_rawFormula_hasPolynomialSignDescription
    (hQQE : PublishedQuantitativeRealQE)
    {α : Type} [Finite α] (φ : Language.ring.Formula α) :
    HasPolynomialSignDescription {v | φ.Realize v} := by
  classical
  letI := Fintype.ofFinite α
  obtain ⟨blocks, s, D, p, b, _, _, heq⟩ :=
    rawFormula_prenex_polynomial_representation φ
  rw [heq]
  exact published_polynomialPrenexSet_hasPolynomialSignDescription hQQE blocks p b

/-- Definability permits arbitrary named real constants. Finiteness of the
formula supplies finitely many constant names; their actual values are retained
exactly in the projection fiber, without a magnitude or algebraicity premise. -/
theorem published_definable_hasPolynomialSignDescription_of_quantitativeQE
    (hQQE : PublishedQuantitativeRealQE)
    {α : Type} [Finite α] (S : Set (α → ℝ))
    (hS : (Set.univ : Set ℝ).Definable Language.ring S) :
    HasPolynomialSignDescription S := by
  classical
  obtain ⟨C, _, hC⟩ := Set.definable_iff_finitely_definable.mp hS
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hC
  have h := projectionFiber_hasPolynomialSignDescription
    {v | φ.Realize v} (published_rawFormula_hasPolynomialSignDescription hQQE φ)
    (fun c : (C : Set ℝ) => (c : ℝ))
  simpa only [projectionFiber, hφ] using h

/-- A checked implication between the two existing accepted-input interfaces.
The quantitative input remains an explicit parameter; no global instance is
installed and no proof of that published input is supplied. -/
theorem PublishedQuantitativeRealQE.toRealSemialgebraicity
    (hQQE : PublishedQuantitativeRealQE) : PublishedRealSemialgebraicity :=
  ⟨fun S hS => published_definable_hasPolynomialSignDescription_of_quantitativeQE hQQE S hS⟩

end PaperI
