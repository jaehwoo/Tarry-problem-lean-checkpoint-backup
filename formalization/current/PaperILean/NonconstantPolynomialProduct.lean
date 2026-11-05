import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Data.Real.Basic

/-! A nonzero polynomial times a nonconstant polynomial cannot be constant.
The constant zero case is included. This supplies the algebraic product step
in the normal-column argument, without assuming any degree bound. -/

noncomputable section
namespace PaperI

theorem mul_ne_C_of_nonconstant (L G : MvPolynomial (Fin 3) ℝ)
    (hL : L ≠ 0) (hG : ∀ c : ℝ, G ≠ MvPolynomial.C c) (c : ℝ) :
    L * G ≠ MvPolynomial.C c := by
  intro h
  have hG0 : G ≠ 0 := by simpa using hG 0
  have hdeg : MonomialOrder.lex.degree L + MonomialOrder.lex.degree G = 0 := by
    rw [← MonomialOrder.degree_mul hL hG0, h, MonomialOrder.degree_C]
  have hGdeg : MonomialOrder.lex.degree G = 0 := (add_eq_zero.mp hdeg).2
  exact hG _ (MonomialOrder.eq_C_of_degree_eq_zero hGdeg)

theorem zero_of_mul_eq_C_of_nonconstant (L G : MvPolynomial (Fin 3) ℝ)
    (hG : ∀ c : ℝ, G ≠ MvPolynomial.C c) (c : ℝ)
    (h : L * G = MvPolynomial.C c) : L = 0 := by
  by_contra hL
  exact mul_ne_C_of_nonconstant L G hL hG c h

end PaperI
