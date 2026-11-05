import PaperILean.TensorSlotSymmetry
import PaperILean.FullFrameEnergyConvexity

/-! The physical and logarithmic first variations at I250-254.
The logarithm is transported to B^T B by the fixed polar factor; B and H
are not assumed to commute. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem hasDerivAt_frame_exponential_zero {n : ℕ}
    (B H : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => B * NormedSpace.exp ℝ (t • H)) (B * H) 0 := by
  simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) H (0 : ℝ)).const_mul B

theorem hasDerivAt_matrixFullHSNorm_sq_frame_zero {n : ℕ}
    (B H : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => (matrixFullHSNorm (B * NormedSpace.exp ℝ (t • H))) ^ 2)
      (2 * Matrix.trace (Bᵀ * B * H)) 0 := by
  have he (i j : Fin n) :
      HasDerivAt (fun t : ℝ => (B * NormedSpace.exp ℝ (t • H)) i j) ((B * H) i j) 0 :=
    ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_frame_exponential_zero B H)
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ => (he i j).pow 2))
  norm_num only [zero_smul, NormedSpace.exp_zero, mul_one, Nat.reduceSub, pow_one,
    Nat.cast_ofNat] at hs
  convert hs using 1
  · funext t
    exact matrixFullHSNorm_sq _
  · simp only [Matrix.mul_assoc, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring

theorem frame_rightGram_eq_polar_conjugate (B : PositiveFrame) :
    B.valᵀ * B.val = orthogonalConjugate (star (framePolarFactor B)) (B.val * B.valᵀ) := by
  rw [← sourcePositiveSqrt_mul_self (B.val * B.valᵀ) (positiveFrame_gram_posDef B)]
  simp only [orthogonalConjugate, unitary.coe_star, star_star]
  rw [← Matrix.mul_assoc, frame_polar_transpose_decomposition, Matrix.mul_assoc,
    frame_polar_decomposition]

theorem frame_rightGram_posDef (B : PositiveFrame) : (B.valᵀ * B.val).PosDef := by
  rw [frame_rightGram_eq_polar_conjugate]
  exact orthogonalConjugate_posDef _ _ (positiveFrame_gram_posDef B)

theorem hasDerivAt_frameLogEnergyCurve_zero (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    HasDerivAt (frameLogEnergyCurve B H) (4 * Matrix.trace (CFC.log (B.valᵀ * B.val) * H)) 0 := by
  rw [frameLogEnergyCurve_eq_source B H hH]
  have ht : Matrix.trace (CFC.log (B.val * B.valᵀ) * orthogonalConjugate (framePolarFactor B) H) =
      Matrix.trace (CFC.log (B.valᵀ * B.val) * H) := by
    rw [← trace_orthogonalConjugate (star (framePolarFactor B))
      (CFC.log (B.val * B.valᵀ) * orthogonalConjugate (framePolarFactor B) H),
      orthogonalConjugate_mul, orthogonalConjugate_star_inverse,
      ← matrix_log_orthogonalConjugate (star (framePolarFactor B)) _ (positiveFrame_gram_posDef B),
      ← frame_rightGram_eq_polar_conjugate]
  simpa only [ht] using hasDerivAt_sourceMatrixLogEnergyCurve_zero _ (positiveFrame_gram_posDef B)
    (orthogonalConjugate (framePolarFactor B) H) (orthogonalConjugate_isSymm _ H hH)

end PaperI
