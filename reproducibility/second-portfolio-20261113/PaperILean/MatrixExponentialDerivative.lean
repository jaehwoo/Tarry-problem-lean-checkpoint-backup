import PaperILean.MatrixLogDerivative

/-! Differentiate the actual exponential along a commuting matrix curve.
The factorial majorant is summable for every fixed radius. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem factorial_inverse_mul_succ (n : ℕ) :
    ((n+1).factorial : ℝ)⁻¹ * (n+1 : ℝ) = (n.factorial : ℝ)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem matrix_exp_term_hasDerivAt
    (f : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (D : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ)
    (hf : HasDerivAt f D x) (hc : Commute (f x) D) (n : ℕ) :
    HasDerivAt (fun y => ((n+1).factorial : ℝ)⁻¹ • f y^(n+1))
      ((n.factorial : ℝ)⁻¹ • f x^n * D) x := by
  have h := (matrix_hasDerivAt_pow_succ f D x hf hc n).const_smul
    ((n+1).factorial : ℝ)⁻¹
  simpa only [smul_smul, factorial_inverse_mul_succ, Matrix.smul_mul] using h

theorem matrix_exp_derivative_term_norm_le
    (B D : Matrix (Fin 3) (Fin 3) ℝ) (r C : ℝ) (hr : 0 ≤ r)
    (hB : ‖B‖ ≤ r) (hD : ‖D‖ ≤ C) (n : ℕ) :
    ‖(n.factorial : ℝ)⁻¹ • B^n * D‖ ≤ ((n.factorial : ℝ)⁻¹ * r^n)*C := by
  rw [Matrix.smul_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h : ‖B^n * D‖ ≤ r^n*C := by
    calc
      ‖B^n * D‖ ≤ ‖B^n‖*‖D‖ := norm_mul_le _ _
      _ ≤ r^n*C := mul_le_mul
        ((norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg B) hB n))
        hD (norm_nonneg D) (pow_nonneg hr n)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h
    (show 0 ≤ (n.factorial : ℝ)⁻¹ by positivity)

theorem matrix_exp_hasDerivAt_on
    (f f' : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : Set ℝ)
    (hs : IsOpen s) (hconn : IsPreconnected s) (r C : ℝ) (hr : 0 ≤ r)
    (hf : ∀ x ∈ s, HasDerivAt f (f' x) x)
    (hc : ∀ x ∈ s, Commute (f x) (f' x))
    (hb : ∀ x ∈ s, ‖f x‖ ≤ r) (hd : ∀ x ∈ s, ‖f' x‖ ≤ C)
    (x : ℝ) (hx : x ∈ s) :
    HasDerivAt (fun y => NormedSpace.exp ℝ (f y))
      (NormedSpace.exp ℝ (f x) * f' x) x := by
  have hscalar : Summable (fun n : ℕ => (n.factorial : ℝ)⁻¹ * r^n) := by
    simpa only [smul_eq_mul] using (NormedSpace.expSeries_summable' (𝕂 := ℝ) r)
  have hinit : Summable (fun n : ℕ => ((n+1).factorial : ℝ)⁻¹ • f x^(n+1)) :=
    (NormedSpace.expSeries_summable' (𝕂 := ℝ) (f x)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hsum := hasDerivAt_tsum_of_isPreconnected (hscalar.mul_right C) hs hconn
    (fun n y hy => matrix_exp_term_hasDerivAt f (f' y) y (hf y hy) (hc y hy) n)
    (fun n y hy => matrix_exp_derivative_term_norm_le (f y) (f' y) r C hr
      (hb y hy) (hd y hy) n) hx hinit hx
  have hseries := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (f x)).mul_right (f' x)
  rw [hseries.tsum_eq] at hsum
  have h := hsum.add_const (1 : Matrix (Fin 3) (Fin 3) ℝ)
  simpa only [← matrix_exp_sub_one_eq_tsum, sub_add_cancel] using h

end PaperI
