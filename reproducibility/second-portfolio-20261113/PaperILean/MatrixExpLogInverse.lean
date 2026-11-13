import PaperILean.MatrixExponentialDerivative
import PaperILean.MatrixLogInverse

/-! I327: Exp(L(A)) = A on the entire ordinary convergence ball.
Differentiate the literal series along I+tX. No logarithm inverse identity is
assumed, and every commutation and uniform-on-the-path bound is proved. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def matrixRadialLogDerivative (X : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ := (∑' n : ℕ, (-(t • X))^n)*X

theorem matrixLogSeries_commute (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (h : Commute A B) : Commute (matrixLogSeries A) B := by
  apply Commute.tsum_left
  intro n
  exact ((h.sub_left (Commute.one_left B)).pow_left (n+1)).smul_left _

theorem matrix_radial_norm_le (X : Matrix (Fin 3) (Fin 3) ℝ)
    (r t : ℝ) (ht : t ∈ Ioo (-r) r) : ‖t • X‖ ≤ r*‖X‖ := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_lt.mpr ht).le (norm_nonneg X)

theorem matrixLogSeries_radial_hasDerivAt
    (X : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hr : 0 < r)
    (hsmall : r*‖X‖ < 1) (t : ℝ) (ht : t ∈ Ioo (-r) r) :
    HasDerivAt (fun y : ℝ => matrixLogSeries (1+y • X))
      (matrixRadialLogDerivative X t) t := by
  have h := matrixLogSeries_hasDerivAt_on (fun y : ℝ => 1+y • X) (fun _ => X)
    (Ioo (-r) r) isOpen_Ioo (convex_Ioo (-r) r).isPreconnected
    (r*‖X‖) ‖X‖ (by positivity) hsmall
    (fun y _ => by simpa only [one_smul] using ((hasDerivAt_id y).smul_const X).const_add 1)
    (fun y _ => by simpa only [add_sub_cancel_left] using (Commute.refl X).smul_left y)
    (fun y hy => by simpa only [add_sub_cancel_left] using matrix_radial_norm_le X r y hy)
    (fun _ _ => le_rfl) t ht
  simpa only [matrixRadialLogDerivative, add_sub_cancel_left] using h

theorem matrixRadialLogDerivative_norm_le
    (X : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hsmall : r*‖X‖ < 1) (t : ℝ) (ht : t ∈ Ioo (-r) r) :
    ‖matrixRadialLogDerivative X t‖ ≤ (1-r*‖X‖)⁻¹*‖X‖ := by
  have hb := matrix_radial_norm_le X r t ht
  have hs : Summable (fun n : ℕ => (-(t • X))^n) :=
    summable_geometric_of_norm_lt_one (by simpa only [norm_neg] using hb.trans_lt hsmall)
  rw [matrixRadialLogDerivative, ← hs.tsum_mul_right X]
  apply tsum_of_norm_bounded ((hasSum_geometric_of_lt_one (by positivity : 0 ≤ r*‖X‖)
    hsmall).mul_right ‖X‖)
  intro n
  exact matrixLogSeries_derivative_term_norm_le (t • X) X (r*‖X‖) ‖X‖
    (by positivity) hb le_rfl n

theorem matrixLogSeries_radial_norm_le
    (X : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hsmall : r*‖X‖ < 1) (t : ℝ) (ht : t ∈ Ioo (-r) r) :
    ‖matrixLogSeries (1+t • X)‖ ≤ (r*‖X‖)/(1-r*‖X‖) := by
  have hb := matrix_radial_norm_le X r t ht
  have hdom : ‖1+t • X-1‖ < 1 := by
    simpa only [add_sub_cancel_left] using hb.trans_lt hsmall
  have h := matrixLogSeries_norm_le (1+t • X) hdom
  simp only [add_sub_cancel_left] at h
  apply h.trans
  apply (div_le_div_iff₀ (by linarith : 0 < 1-‖t • X‖)
    (by linarith : 0 < 1-r*‖X‖)).mpr
  nlinarith

theorem matrixLogSeries_radial_commute_derivative
    (X : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    Commute (matrixLogSeries (1+t • X)) (matrixRadialLogDerivative X t) := by
  have h := matrixLogSeries_commute (1+t • X) X
    ((Commute.one_left X).add_left ((Commute.refl X).smul_left t))
  apply Commute.mul_right _ h
  apply Commute.tsum_right
  intro n
  exact ((h.smul_right t).neg_right).pow_right n

theorem matrixRadialLogDerivative_mul
    (X : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (ht : ‖t • X‖ < 1) :
    matrixRadialLogDerivative X t * (1+t • X) = X := by
  have hc : Commute X (1+t • X) :=
    (Commute.one_right X).add_right ((Commute.refl X).smul_right t)
  have hgeom := matrixLogSeries_geometric_cancel (1+t • X)
    (by simpa only [add_sub_cancel_left] using ht)
  simp only [add_sub_cancel_left] at hgeom
  rw [matrixRadialLogDerivative, mul_assoc, hc.eq, ← mul_assoc, hgeom, one_mul]

theorem matrix_exp_neg_radial_log_hasDerivAt
    (X : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hr : 0 < r)
    (hsmall : r*‖X‖ < 1) (t : ℝ) (ht : t ∈ Ioo (-r) r) :
    HasDerivAt (fun y : ℝ => NormedSpace.exp ℝ (-matrixLogSeries (1+y • X)))
      (NormedSpace.exp ℝ (-matrixLogSeries (1+t • X)) * (-matrixRadialLogDerivative X t)) t := by
  apply matrix_exp_hasDerivAt_on (fun y : ℝ => -matrixLogSeries (1+y • X))
    (fun y => -matrixRadialLogDerivative X y) (Ioo (-r) r)
    isOpen_Ioo (convex_Ioo (-r) r).isPreconnected
    ((r*‖X‖)/(1-r*‖X‖)) ((1-r*‖X‖)⁻¹*‖X‖)
    (div_nonneg (by positivity) (by linarith))
    (fun y hy => (matrixLogSeries_radial_hasDerivAt X r hr hsmall y hy).neg)
    (fun y _ => (matrixLogSeries_radial_commute_derivative X y).neg_left.neg_right)
    (fun y hy => by simpa only [norm_neg] using matrixLogSeries_radial_norm_le X r hr.le hsmall y hy)
    (fun y hy => by simpa only [norm_neg] using matrixRadialLogDerivative_norm_le X r hr.le hsmall y hy)
    t ht

theorem matrix_exp_neg_radial_log_mul_hasDerivAt_zero
    (X : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hr : 0 < r)
    (hsmall : r*‖X‖ < 1) (t : ℝ) (ht : t ∈ Ioo (-r) r) :
    HasDerivAt (fun y : ℝ => NormedSpace.exp ℝ (-matrixLogSeries (1+y • X))*(1+y • X)) 0 t := by
  have hg : HasDerivAt (fun y : ℝ => 1+y • X) X t := by
    simpa only [one_smul] using ((hasDerivAt_id t).smul_const X).const_add 1
  have h := (matrix_exp_neg_radial_log_hasDerivAt X r hr hsmall t ht).mul hg
  have hc := matrixRadialLogDerivative_mul X t ((matrix_radial_norm_le X r t ht).trans_lt hsmall)
  simpa only [mul_assoc, neg_mul, hc, mul_neg, neg_add_cancel] using h

theorem matrix_exp_neg_radial_log_mul_eq_one
    (X : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (hr : 0 < r)
    (hsmall : r*‖X‖ < 1) (t : ℝ) (ht : t ∈ Ioo (-r) r) :
    NormedSpace.exp ℝ (-matrixLogSeries (1+t • X))*(1+t • X) = 1 := by
  have hd (y : ℝ) (hy : y ∈ Ioo (-r) r) :=
    matrix_exp_neg_radial_log_mul_hasDerivAt_zero X r hr hsmall y hy
  have h := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-r) r).isPreconnected
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) ht
    (show (0 : ℝ) ∈ Ioo (-r) r by constructor <;> linarith)
  simpa [matrixLogSeries_one] using h

theorem matrix_exp_matrixLogSeries_one_add
    (X : Matrix (Fin 3) (Fin 3) ℝ) (hX : ‖X‖ < 1) :
    NormedSpace.exp ℝ (matrixLogSeries (1+X)) = 1+X := by
  by_cases hzero : X = 0
  · simp [hzero, matrixLogSeries_one]
  have hn : 0 < ‖X‖ := norm_pos_iff.mpr hzero
  obtain ⟨q, hqX, hq1⟩ := exists_between hX
  have hr : 0 < q/‖X‖ := div_pos (hn.trans hqX) hn
  have hr1 : 1 < q/‖X‖ := (lt_div_iff₀ hn).mpr (by simpa using hqX)
  have hsmall : (q/‖X‖)*‖X‖ < 1 := by rwa [div_mul_cancel₀ _ hn.ne']
  have h := matrix_exp_neg_radial_log_mul_eq_one X (q/‖X‖) hr hsmall 1
    (by constructor <;> linarith)
  simp only [one_smul] at h
  have hm := congrArg (fun A => NormedSpace.exp ℝ (matrixLogSeries (1+X))*A) h
  dsimp only at hm
  rw [← mul_assoc, ← Matrix.exp_add_of_commute ℝ _ _ (Commute.refl _).neg_right] at hm
  simpa using hm.symm

theorem matrix_exp_matrixLogSeries
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ‖A-1‖ < 1) :
    NormedSpace.exp ℝ (matrixLogSeries A) = A := by
  have heq : 1+(A-1) = A := by abel
  simpa only [heq] using matrix_exp_matrixLogSeries_one_add (A-1) hA

end PaperI
