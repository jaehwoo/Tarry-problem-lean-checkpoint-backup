import PaperILean.NormalColumnRepresentation
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-! The total-degree obstruction for the affine pair at manuscript I:693.
Both scalar multipliers are affine in y,z. The second factor must be
nonconstant; its constant and zero cases are deliberately excluded. -/

noncomputable section
namespace PaperI
open MvPolynomial

theorem polynomial_totalDegree_mul_eq (f g : MvPolynomial (Fin 3) ℝ)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).totalDegree = f.totalDegree + g.totalDegree := by
  rw [← degree_degLexDegree, MonomialOrder.degree_mul hf hg,
    Finsupp.degree_add, degree_degLexDegree, degree_degLexDegree]

theorem polynomial_totalDegree_neg (f : MvPolynomial (Fin 3) ℝ) :
    (-f).totalDegree = f.totalDegree := by
  rw [← degree_degLexDegree, MonomialOrder.degree_neg, degree_degLexDegree]

theorem normalScalarPolynomial_totalDegree_le (v : Fin 3 → ℝ) :
    (normalScalarPolynomial v).totalDegree ≤ 1 := by
  unfold normalScalarPolynomial
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simp)
  · exact (totalDegree_mul _ _).trans (by simp)

theorem normalScalarPolynomial_eq_C_implies_linear_zero (v : Fin 3 → ℝ)
    (c : ℝ) (h : normalScalarPolynomial v = C c) : v 0 = 0 ∧ v 1 = 0 := by
  have hc := congrArg (MvPolynomial.eval (0 : PhysicalSpace)) h
  have hy := congrArg (MvPolynomial.eval ![(0 : ℝ), 1, 0]) h
  have hz := congrArg (MvPolynomial.eval ![(0 : ℝ), 0, 1]) h
  simp only [eval_normalScalarPolynomial, eval_C] at hc hy hz
  simp only [Pi.zero_apply, mul_zero, add_zero] at hc
  simp at hy hz
  constructor <;> linarith

theorem normalScalarPolynomial_totalDegree_eq_one (v : Fin 3 → ℝ)
    (hv : v 0 ≠ 0 ∨ v 1 ≠ 0) : (normalScalarPolynomial v).totalDegree = 1 := by
  have hle := normalScalarPolynomial_totalDegree_le v
  have hne : (normalScalarPolynomial v).totalDegree ≠ 0 := by
    intro h
    have hh := normalScalarPolynomial_eq_C_implies_linear_zero v _
      (totalDegree_eq_zero_iff_eq_C.mp h)
    rcases hv with hv | hv
    · exact hv hh.1
    · exact hv hh.2
  omega

theorem affineNormalPair_multiplier_degree (v w : Fin 3 → ℝ)
    (hv : v 0 ≠ 0 ∨ v 1 ≠ 0) :
    (normalScalarPolynomial w - X 2 * normalScalarPolynomial v).totalDegree = 2 := by
  have hL := normalScalarPolynomial_totalDegree_eq_one v hv
  have hLn : normalScalarPolynomial v ≠ 0 := by
    intro h
    simp [h] at hL
  have hXL : (X 2 * normalScalarPolynomial v).totalDegree = 2 := by
    rw [polynomial_totalDegree_mul_eq _ _ (X_ne_zero 2) hLn, totalDegree_X, hL]
  rw [sub_eq_add_neg, totalDegree_add_eq_right_of_totalDegree_lt]
  · rw [polynomial_totalDegree_neg, hXL]
  · rw [polynomial_totalDegree_neg, hXL]
    exact lt_of_le_of_lt (normalScalarPolynomial_totalDegree_le w) (by decide)

theorem affineNormalPair_product_degree_ge_three (v w : Fin 3 → ℝ)
    (hv : v 0 ≠ 0 ∨ v 1 ≠ 0) (G : MvPolynomial (Fin 3) ℝ)
    (hG : ∀ c : ℝ, G ≠ C c) :
    3 ≤ ((normalScalarPolynomial w - X 2 * normalScalarPolynomial v) * G).totalDegree := by
  have hR := affineNormalPair_multiplier_degree v w hv
  have hRn : normalScalarPolynomial w - X 2 * normalScalarPolynomial v ≠ 0 := by
    intro h
    simp [h] at hR
  have hGn : G ≠ 0 := by simpa using hG 0
  have hGd : G.totalDegree ≠ 0 := by
    intro h
    exact hG _ (totalDegree_eq_zero_iff_eq_C.mp h)
  rw [polynomial_totalDegree_mul_eq _ _ hRn hGn, hR]
  omega

theorem constant_sub_constant_mul_X_totalDegree_le (c0 c1 : ℝ) :
    (C c0 - C c1 * (X 2 : MvPolynomial (Fin 3) ℝ)).totalDegree ≤ 1 := by
  rw [sub_eq_add_neg]
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · rw [polynomial_totalDegree_neg]
    exact (totalDegree_mul _ _).trans (by simp)

theorem affineNormalPair_product_ne_linear (v w : Fin 3 → ℝ)
    (hv : v 0 ≠ 0 ∨ v 1 ≠ 0) (G : MvPolynomial (Fin 3) ℝ)
    (hG : ∀ c : ℝ, G ≠ C c) (c0 c1 : ℝ) :
    (normalScalarPolynomial w - X 2 * normalScalarPolynomial v) * G ≠
      C c0 - C c1 * X 2 := by
  intro h
  have hlo := affineNormalPair_product_degree_ge_three v w hv G hG
  rw [h] at hlo
  have hhi := constant_sub_constant_mul_X_totalDegree_le c0 c1
  omega

end PaperI
