import PaperILean.RotationExponential

/-! I327: the actual logarithm power series at identity.
The series is proved convergent on its stated domain. Its local inverse and
skew-image properties are separate unresolved obligations, not hypotheses here. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def matrixLogSeriesCoefficient (n : ℕ) : ℝ := (-1 : ℝ)^n / (n+1 : ℝ)

def matrixLogSeries (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑' n : ℕ, matrixLogSeriesCoefficient n • (A-1)^(n+1)

theorem matrixLogSeriesCoefficient_abs_le_one (n : ℕ) :
    |matrixLogSeriesCoefficient n| ≤ 1 := by
  have hn : (1 : ℝ) ≤ n+1 := by have h := Nat.cast_nonneg (α := ℝ) n; linarith
  simp only [matrixLogSeriesCoefficient, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n+1), one_div]
  exact inv_le_one_of_one_le₀ hn

theorem matrixLogSeries_summable (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ‖A-1‖ < 1) :
    Summable (fun n : ℕ => matrixLogSeriesCoefficient n • (A-1)^(n+1)) :=
  matrix_power_series_summable (A-1) hA _ matrixLogSeriesCoefficient_abs_le_one

theorem matrixLogSeries_hasSum (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ‖A-1‖ < 1) :
    HasSum (fun n : ℕ => matrixLogSeriesCoefficient n • (A-1)^(n+1)) (matrixLogSeries A) :=
  (matrixLogSeries_summable A hA).hasSum

theorem matrixLogSeries_one : matrixLogSeries 1 = 0 := by
  simp [matrixLogSeries]

theorem matrixLogSeries_norm_le (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ‖A-1‖ < 1) :
    ‖matrixLogSeries A‖ ≤ ‖A-1‖ / (1-‖A-1‖) :=
  matrix_power_series_norm_le (A-1) hA _ matrixLogSeriesCoefficient_abs_le_one

def frameConjugateLinear (E : PositiveFrame) :
    Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ where
  toFun := frameConjugate E
  map_add' := by intro A B; simp [frameConjugate, Matrix.mul_add, Matrix.add_mul]
  map_smul' := by intro r A; simp [frameConjugate, Matrix.mul_smul, Matrix.smul_mul]

def frameConjugateCLM (E : PositiveFrame) :
    Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toContinuousLinearMap (frameConjugateLinear E)

theorem frameConjugateCLM_apply (E : PositiveFrame) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    frameConjugateCLM E A = frameConjugate E A := rfl

theorem frameConjugate_smul (E : PositiveFrame) (r : ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) : frameConjugate E (r • A) = r • frameConjugate E A :=
  (frameConjugateLinear E).map_smul r A

theorem frameConjugate_pow (E : PositiveFrame) (A : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) :
    frameConjugate E (A^n) = (frameConjugate E A)^n := by
  induction n with
  | zero => simp only [pow_zero, frameConjugate_one]
  | succ n ih => rw [pow_succ, frameConjugate_mul, ih, pow_succ]

theorem frameConjugate_matrixLogSeries (E : PositiveFrame)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ‖A-1‖ < 1) :
    frameConjugate E (matrixLogSeries A) = matrixLogSeries (frameConjugate E A) := by
  have h := (frameConjugateCLM E).map_tsum (matrixLogSeries_summable A hA)
  simpa only [frameConjugateCLM_apply, frameConjugate_smul, frameConjugate_pow,
    frameConjugate_sub, frameConjugate_one, matrixLogSeries] using h

theorem frameConjugate_matrixLogSeries_summable (E : PositiveFrame)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ‖A-1‖ < 1) :
    Summable (fun n : ℕ => matrixLogSeriesCoefficient n • (frameConjugate E A-1)^(n+1)) := by
  have h := (frameConjugateCLM E).summable (matrixLogSeries_summable A hA)
  simpa only [frameConjugateCLM_apply, frameConjugate_smul, frameConjugate_pow,
    frameConjugate_sub, frameConjugate_one] using h

theorem diagonalFrameConjugate_matrixLogSeries (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ‖A-1‖ < 1) :
    diagonalFrameConjugate e (matrixLogSeries A) =
      matrixLogSeries (diagonalFrameConjugate e A) :=
  frameConjugate_matrixLogSeries (positiveDiagonalFrame e he) A hA

theorem matrixLogSeries_transpose (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ‖A-1‖ < 1) :
    (matrixLogSeries A)ᵀ = matrixLogSeries Aᵀ := by
  let L : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℝ ℝ).toLinearMap
  have h := L.map_tsum (matrixLogSeries_summable A hA)
  change (∑' n : ℕ, matrixLogSeriesCoefficient n • (A-1)^(n+1))ᵀ =
    ∑' n : ℕ, (matrixLogSeriesCoefficient n • (A-1)^(n+1))ᵀ at h
  simpa only [matrixLogSeries, Matrix.transpose_smul, Matrix.transpose_pow,
    Matrix.transpose_sub, Matrix.transpose_one] using h

def rotationLogSeries (O : rotationGroup3) : Matrix (Fin 3) (Fin 3) ℝ :=
  matrixLogSeries (rotationMatrix O)

theorem rotationLogSeries_one : rotationLogSeries 1 = 0 := matrixLogSeries_one

theorem rotationLogSeries_hasSum (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : t < 1/10) (O : rotationGroup3)
    (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    HasSum (fun n : ℕ => matrixLogSeriesCoefficient n • (rotationMatrix O-1)^(n+1))
      (rotationLogSeries O) :=
  matrixLogSeries_hasSum _ (rotationNeighborhood_source_ordinary_domain e he t ht O hO)

theorem rotationLogSeries_inv_eq_transpose (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : t < 1/10) (O : rotationGroup3)
    (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    rotationLogSeries O⁻¹ = (rotationLogSeries O)ᵀ := by
  unfold rotationLogSeries
  rw [rotationMatrix_inv]
  exact (matrixLogSeries_transpose _
    (rotationNeighborhood_source_ordinary_domain e he t ht O hO)).symm

theorem rotationLogSeries_conjugate_norm_lt (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : t < 1/10) (O : rotationGroup3)
    (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    ‖diagonalFrameConjugate e (rotationLogSeries O)‖ < t / (1-t) := by
  have hdom := rotationNeighborhood_source_ordinary_domain e he t ht O hO
  have hn : ‖diagonalFrameConjugate e (rotationMatrix O-1)‖ < t := hO
  have ht1 : t < 1 := by linarith
  have hsub : diagonalFrameConjugate e (rotationMatrix O) - 1 =
      diagonalFrameConjugate e (rotationMatrix O-1) := by
    change frameConjugate (positiveDiagonalFrame e he) (rotationMatrix O) - 1 =
      frameConjugate (positiveDiagonalFrame e he) (rotationMatrix O-1)
    rw [frameConjugate_sub, frameConjugate_one]
  unfold rotationLogSeries
  rw [diagonalFrameConjugate_matrixLogSeries e he _ hdom]
  have h := matrixLogSeries_norm_le (diagonalFrameConjugate e (rotationMatrix O))
    (by rw [hsub]; exact hn.trans ht1)
  rw [hsub] at h
  apply h.trans_lt
  apply (div_lt_div_iff₀ (by linarith : 0 < 1-‖diagonalFrameConjugate e (rotationMatrix O-1)‖)
    (by linarith : 0 < 1-t)).mpr
  nlinarith

theorem rotationLogSeries_conjugate_norm_lt_two (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : t < 1/10) (O : rotationGroup3)
    (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    ‖diagonalFrameConjugate e (rotationLogSeries O)‖ < 2*t := by
  have hn := rotationLogSeries_conjugate_norm_lt e he t ht O hO
  have hp : 0 < t := (norm_nonneg _).trans_lt hO
  apply hn.trans_le
  apply (div_le_iff₀ (by linarith : 0 < 1-t)).mpr
  nlinarith

theorem matrix_exp_sub_one_norm_lt_one_of_lt_half (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ‖H‖ < 1/2) : ‖NormedSpace.exp ℝ H - 1‖ < 1 := by
  have h := matrix_exp_sub_one_norm_le_two H hH.le
  linarith

theorem anisotropicSkewBall_source_fixed_radius (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : t < 1/10) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H ∈ anisotropicSkewBall e ((10/9)*t)) : ‖H‖ < 1/2 := by
  have h := anisotropicSkewBall_ordinary_norm e he ((10/9)*t) H hH
  linarith

theorem rotationLogSeries_conjugate_norm_lt_ten_ninths (e : Fin 3 → ℝ)
    (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10) (O : rotationGroup3)
    (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    ‖diagonalFrameConjugate e (rotationLogSeries O)‖ < (10/9)*t := by
  have hn := rotationLogSeries_conjugate_norm_lt e he t ht O hO
  have hp : 0 < t := (norm_nonneg _).trans_lt hO
  apply hn.trans_le
  apply (div_le_iff₀ (by linarith : 0 < 1-t)).mpr
  nlinarith

end PaperI
