import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-! I638: elementary coefficient estimates for the independent polynomial-root
growth route. No real quantifier elimination or graph continuity is assumed. -/

noncomputable section
open Filter Polynomial
open scoped BigOperators
namespace PaperI

def polynomialCoefficientMass (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|

theorem polynomialCoefficientMass_nonneg (p : Polynomial ℝ) :
    0 ≤ polynomialCoefficientMass p :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem polynomial_abs_eval_le_mass (p : Polynomial ℝ) {t : ℝ} (ht : |t| ≤ 1) :
    |p.eval t| ≤ polynomialCoefficientMass p := by
  rw [Polynomial.eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul, abs_pow]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) ht)

theorem polynomial_abs_eval_le_mass_mul_pow (p : Polynomial ℝ) {P : ℝ} (hP : 1 ≤ P) :
    |p.eval P| ≤ polynomialCoefficientMass p * P ^ p.natDegree := by
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  rw [Polynomial.eval_eq_sum_range, polynomialCoefficientMass, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul, abs_pow, abs_of_nonneg hP0]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hP (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (abs_nonneg _)

theorem polynomial_exists_positive_power_upper_bound (p : Polynomial ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∀ P : ℝ, 1 ≤ P → |p.eval P| ≤ B * P ^ N := by
  refine ⟨polynomialCoefficientMass p + 1, by linarith [polynomialCoefficientMass_nonneg p],
    p.natDegree, ?_⟩
  intro P hP
  exact (polynomial_abs_eval_le_mass_mul_pow p hP).trans
    (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (by linarith) _))

theorem nonzero_polynomial_eventually_abs_lower (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ P : ℝ in atTop, b ≤ |p.eval P| := by
  by_cases hd : 0 < p.degree
  · exact ⟨1, zero_lt_one, (p.abs_tendsto_atTop hd).eventually_ge_atTop 1⟩
  · have he : p = Polynomial.C (p.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hd)
    have hc : p.coeff 0 ≠ 0 := by
      intro h
      exact hp (by simpa [h] using he)
    refine ⟨|p.coeff 0|, abs_pos.mpr hc, Filter.Eventually.of_forall ?_⟩
    intro P
    have hev := congrArg (Polynomial.eval P) he
    simpa only [Polynomial.eval_C] using le_of_eq (congrArg abs hev.symm)

theorem polynomial_constant_abs_le_small_root_mul_mass (p : Polynomial ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : p.eval t = 0) :
    |p.coeff 0| ≤ t * polynomialCoefficientMass p.divX := by
  have he := congrArg (Polynomial.eval t) (Polynomial.X_mul_divX_add p)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, hr] at he
  have hc : p.coeff 0 = -(t * p.divX.eval t) := by linarith
  rw [hc, abs_neg, abs_mul, abs_of_nonneg ht0]
  exact mul_le_mul_of_nonneg_left
    (polynomial_abs_eval_le_mass p.divX (by rwa [abs_of_nonneg ht0])) ht0

end PaperI
