import PaperILean.RotationChartDomains
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecificLimits.Normed

/-! I327: the actual matrix exponential, its rotation image and conjugation.
A geometric-series majorant provides fixed anisotropic radius bounds. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem matrix_exp_skew_orthogonal (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : Hᵀ = -H) :
    NormedSpace.exp ℝ H * (NormedSpace.exp ℝ H)ᵀ = 1 := by
  rw [← Matrix.exp_transpose, hH,
    ← Matrix.exp_add_of_commute ℝ H (-H) (Commute.refl H).neg_right]
  simp

theorem matrix_exp_half_square (A : Matrix (Fin 3) (Fin 3) ℝ) :
    NormedSpace.exp ℝ A =
      NormedSpace.exp ℝ ((1 / 2 : ℝ) • A) * NormedSpace.exp ℝ ((1 / 2 : ℝ) • A) := by
  rw [← Matrix.exp_add_of_commute ℝ _ _ (Commute.refl _), ← add_smul]
  norm_num

theorem matrix_exp_det_nonneg (A : Matrix (Fin 3) (Fin 3) ℝ) :
    0 ≤ (NormedSpace.exp ℝ A).det := by
  rw [matrix_exp_half_square A, Matrix.det_mul]
  exact mul_self_nonneg _

theorem matrix_exp_skew_det (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : Hᵀ = -H) :
    (NormedSpace.exp ℝ H).det = 1 := by
  have h := congrArg Matrix.det (matrix_exp_skew_orthogonal H hH)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  nlinarith [matrix_exp_det_nonneg H]

theorem matrix_exp_skew_mem_specialOrthogonalGroup (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : Hᵀ = -H) :
    NormedSpace.exp ℝ H ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  refine ⟨?_, matrix_exp_skew_det H hH⟩
  apply (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mpr
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    using matrix_exp_skew_orthogonal H hH

def skewRotationExp (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : Hᵀ = -H) : rotationGroup3 :=
  ⟨⟨NormedSpace.exp ℝ H, (matrix_exp_skew_mem_specialOrthogonalGroup H hH).1⟩,
    matrix_exp_skew_det H hH⟩

theorem rotationMatrix_skewRotationExp (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : Hᵀ = -H) :
    rotationMatrix (skewRotationExp H hH) = NormedSpace.exp ℝ H := rfl

theorem frameConjugate_exp (E : PositiveFrame) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    frameConjugate E (NormedSpace.exp ℝ A) = NormedSpace.exp ℝ (frameConjugate E A) := by
  exact (Matrix.exp_conj' ℝ E.val A
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr E.property.ne'))).symm

theorem diagonalFrameConjugate_exp (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    diagonalFrameConjugate e (NormedSpace.exp ℝ A) =
      NormedSpace.exp ℝ (diagonalFrameConjugate e A) :=
  frameConjugate_exp (positiveDiagonalFrame e he) A

theorem geometric_succ_hasSum (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => r^(n+1)) (r / (1-r)) := by
  simpa only [pow_succ, div_eq_mul_inv, mul_comm] using
    (hasSum_geometric_of_lt_one hr hr1).mul_right r

theorem matrix_smul_pow_succ_norm_le (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : ℝ) (hc : |c| ≤ 1) (n : ℕ) : ‖c • A^(n+1)‖ ≤ ‖A‖^(n+1) := by
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |c| * ‖A^(n+1)‖ ≤ 1 * ‖A‖^(n+1) :=
      mul_le_mul hc (norm_pow_le A (n+1)) (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem matrix_power_series_summable (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ‖A‖ < 1) (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) :
    Summable (fun n : ℕ => c n • A^(n+1)) :=
  Summable.of_norm_bounded (fun n => ‖A‖^(n+1))
    (geometric_succ_hasSum ‖A‖ (norm_nonneg _) hA).summable
    (fun n => matrix_smul_pow_succ_norm_le A (c n) (hc n) n)

theorem matrix_power_series_norm_le (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ‖A‖ < 1) (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) :
    ‖∑' n : ℕ, c n • A^(n+1)‖ ≤ ‖A‖ / (1-‖A‖) :=
  tsum_of_norm_bounded (geometric_succ_hasSum ‖A‖ (norm_nonneg _) hA)
    (fun n => matrix_smul_pow_succ_norm_le A (c n) (hc n) n)

theorem matrix_exp_sub_one_eq_tsum (A : Matrix (Fin 3) (Fin 3) ℝ) :
    NormedSpace.exp ℝ A - 1 = ∑' n : ℕ, (((n+1).factorial : ℝ)⁻¹) • A^(n+1) := by
  have h := (NormedSpace.expSeries_summable' (𝕂 := ℝ) A).tsum_eq_zero_add
  rw [(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).tsum_eq] at h
  simpa using (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h))

theorem factorial_inverse_abs_le_one (n : ℕ) : |((n.factorial : ℝ)⁻¹)| ≤ 1 := by
  have h : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  exact inv_le_one_of_one_le₀ h

theorem matrix_exp_sub_one_norm_le (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ‖A‖ < 1) :
    ‖NormedSpace.exp ℝ A - 1‖ ≤ ‖A‖ / (1-‖A‖) := by
  rw [matrix_exp_sub_one_eq_tsum]
  exact matrix_power_series_norm_le A hA _ (fun n => factorial_inverse_abs_le_one (n+1))

theorem matrix_exp_sub_one_norm_le_two (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ‖A‖ ≤ 1 / 2) : ‖NormedSpace.exp ℝ A - 1‖ ≤ 2 * ‖A‖ := by
  have hlt : ‖A‖ < 1 := by linarith
  apply (matrix_exp_sub_one_norm_le A hlt).trans
  apply (div_le_iff₀ (sub_pos.mpr hlt)).mpr
  nlinarith [norm_nonneg A]

theorem skewRotationExp_mem_neighborhood (E : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : Hᵀ = -H) (t : ℝ) (ht : t ≤ 1)
    (hn : ‖frameConjugate E H‖ < t / 2) :
    skewRotationExp H hH ∈ rotationNeighborhood E t := by
  change ‖frameConjugate E (NormedSpace.exp ℝ H - 1)‖ < t
  rw [frameConjugate_sub, frameConjugate_one, frameConjugate_exp]
  have h := matrix_exp_sub_one_norm_le_two (frameConjugate E H) (by linarith)
  linarith

theorem anisotropicSkewBall_exp_subset_neighborhood (e : Fin 3 → ℝ)
    (he : ∀ i, 0 < e i) (t : ℝ) (ht : t ≤ 1) :
    ∀ H ∈ anisotropicSkewBall e (t/2),
      ∃ O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t,
        rotationMatrix O = NormedSpace.exp ℝ H := by
  rintro H ⟨hH, hn⟩
  exact ⟨skewRotationExp H hH, skewRotationExp_mem_neighborhood _ H hH t ht hn, rfl⟩

end PaperI
