import PaperILean.MatrixLogSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! I327 prerequisite: termwise differentiation of the literal matrix logarithm.
Commutation is required explicitly when differentiating powers. The derivative
series is justified by a uniform geometric majorant on each stated open set. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem matrix_hasDerivAt_pow_succ
    (f : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (D : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ)
    (hf : HasDerivAt f D x) (hc : Commute (f x) D) (n : ℕ) :
    HasDerivAt (fun y => f y ^ (n+1)) ((n+1 : ℝ) • (f x ^ n * D)) x := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    convert ih.mul hf using 1
    simp only [Nat.cast_add, Nat.cast_one, Matrix.smul_mul]
    rw [mul_assoc (f x ^ n) D (f x), ← hc.eq, ← mul_assoc, ← pow_succ]
    simp only [add_smul, one_smul]

theorem matrixLogSeriesCoefficient_mul_succ (n : ℕ) :
    matrixLogSeriesCoefficient n * (n+1 : ℝ) = (-1 : ℝ)^n := by
  unfold matrixLogSeriesCoefficient
  exact div_mul_cancel₀ _ (by positivity)

theorem matrixLogSeries_term_hasDerivAt
    (f : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (D : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ)
    (hf : HasDerivAt f D x) (hc : Commute (f x-1) D) (n : ℕ) :
    HasDerivAt (fun y => matrixLogSeriesCoefficient n • (f y-1)^(n+1))
      ((-(f x-1))^n * D) x := by
  have h := (matrix_hasDerivAt_pow_succ (fun y => f y-1) D x
    (hf.sub_const 1) hc n).const_smul (matrixLogSeriesCoefficient n)
  convert h using 1
  rw [smul_smul, matrixLogSeriesCoefficient_mul_succ]
  rw [show -(f x-1) = (-1 : ℝ) • (f x-1) by simp, smul_pow, Matrix.smul_mul]

theorem matrixLogSeries_derivative_term_norm_le
    (B D : Matrix (Fin 3) (Fin 3) ℝ) (r C : ℝ) (hr : 0 ≤ r)
    (hB : ‖B‖ ≤ r) (hD : ‖D‖ ≤ C) (n : ℕ) :
    ‖(-B)^n * D‖ ≤ r^n * C := by
  calc
    ‖(-B)^n * D‖ ≤ ‖(-B)^n‖ * ‖D‖ := norm_mul_le _ _
    _ ≤ r^n * C := mul_le_mul
      ((norm_pow_le _ _).trans (by simpa using pow_le_pow_left₀ (norm_nonneg B) hB n))
      hD (norm_nonneg D) (pow_nonneg hr n)

theorem matrixLogSeries_hasDerivAt_on
    (f f' : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : Set ℝ)
    (hs : IsOpen s) (hconn : IsPreconnected s) (r C : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hf : ∀ x ∈ s, HasDerivAt f (f' x) x)
    (hc : ∀ x ∈ s, Commute (f x-1) (f' x))
    (hb : ∀ x ∈ s, ‖f x-1‖ ≤ r) (hd : ∀ x ∈ s, ‖f' x‖ ≤ C)
    (x : ℝ) (hx : x ∈ s) :
    HasDerivAt (fun y => matrixLogSeries (f y))
      ((∑' n : ℕ, (-(f x-1))^n) * f' x) x := by
  have hsum := hasDerivAt_tsum_of_isPreconnected
    ((summable_geometric_of_lt_one hr hr1).mul_right C) hs hconn
    (fun n y hy => matrixLogSeries_term_hasDerivAt f (f' y) y (hf y hy) (hc y hy) n)
    (fun n y hy => matrixLogSeries_derivative_term_norm_le (f y-1) (f' y) r C hr
      (hb y hy) (hd y hy) n)
    hx (matrixLogSeries_summable (f x) ((hb x hx).trans_lt hr1)) hx
  have hg : Summable (fun n : ℕ => (-(f x-1))^n) :=
    summable_geometric_of_norm_lt_one (by simpa only [norm_neg] using (hb x hx).trans_lt hr1)
  simpa only [matrixLogSeries, hg.tsum_mul_right] using hsum

theorem matrixLogSeries_geometric_cancel
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ‖A-1‖ < 1) :
    (∑' n : ℕ, (-(A-1))^n) * A = 1 := by
  have h := geom_series_mul_neg (-(A-1)) (by simpa only [norm_neg] using hA)
  convert h using 1 <;> noncomm_ring

end PaperI
