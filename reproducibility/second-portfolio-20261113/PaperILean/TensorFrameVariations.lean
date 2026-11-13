import PaperILean.TensorSlotSpectral
import PaperILean.ExponentialSumCalculus
import PaperILean.OriginalTensorExponential

/-! Actual first and second variations of the full ordered tensor norm.
The source Hessian identity at I284 follows the tensor operator exponential;
the slot operator itself is the sum of actions already defined and proved
HS self-adjoint. No tensor symmetry or nonzero tensor is assumed here. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem tensorFramePullback_diagonal_coordinates {r : ℕ} (T : TensorSpace r)
    (d : Fin 3 → ℝ) (a : Fin r → Fin 3) :
    tensorCoordinates (tensorFramePullback T (Matrix.diagonal d)) a =
      tensorCoordinates T a * ∏ j, d (a j) := by
  have hv : (fun j : Fin r => Matrix.diagonal d *ᵥ (Pi.single (a j) (1 : ℝ) : PhysicalSpace)) =
      fun j : Fin r => d (a j) • (Pi.single (a j) (1 : ℝ) : PhysicalSpace) := by
    funext j i
    by_cases hi : i = a j
    · subst i; simp [Matrix.mulVec_single_one, Matrix.diagonal_apply, Pi.single_apply]
    · simp [Matrix.mulVec_single_one, Matrix.diagonal_apply, Pi.single_apply, hi, Ne.symm hi]
  simp only [tensorCoordinates, tensorFramePullback_apply, hv]
  rw [T.map_smul_univ]
  simp only [smul_eq_mul, mul_comm]

def tensorFrameEnergyCurve {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) : ℝ :=
  (tensorHSNorm (tensorFramePullback T (NormedSpace.exp ℝ (t • H)))) ^ 2

theorem tensorFrameEnergyCurve_eq_sum {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (t : ℝ) :
    tensorFrameEnergyCurve T H t =
      ∑ a : Fin r → Fin 3,
        (tensorCoordinates (tensorFramePullback T
          (symmetricFrameEigenbasis H hH : Matrix (Fin 3) (Fin 3) ℝ)) a) ^ 2 *
            Real.exp (t * (2 * ∑ j, symmetricFrameEigenvalues H hH (a j))) := by
  unfold tensorFrameEnergyCurve
  rw [matrix_exp_symmetricFrame_spectral H hH t]
  simp only [orthogonalConjugate, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, ← tensorFramePullback_mul]
  have hU : (symmetricFrameEigenbasis H hH : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *
      ((symmetricFrameEigenbasis H hH : Matrix (Fin 3) (Fin 3) ℝ)ᵀ)ᵀ = 1 := by
    simpa only [Matrix.transpose_transpose] using
      (real_unitary_transpose_mul (symmetricFrameEigenbasis H hH))
  have hn (S : TensorSpace r) : tensorHSNorm (tensorFramePullback S
      (symmetricFrameEigenbasis H hH : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) = tensorHSNorm S :=
    tensorHSNorm_orthogonal_frame S _ hU
  rw [hn, tensorHSNorm_sq]
  apply Finset.sum_congr rfl
  intro a _
  rw [tensorFramePullback_diagonal_coordinates, ← Real.exp_sum, ← Finset.mul_sum,
    mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

theorem tensorFrameEnergyCurve_eq_weightedSum {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    tensorFrameEnergyCurve T H = weightedExponentialSum Finset.univ
      (fun a : Fin r → Fin 3 => (tensorCoordinates (tensorFramePullback T
        (symmetricFrameEigenbasis H hH : Matrix (Fin 3) (Fin 3) ℝ)) a) ^ 2)
      (fun a => 2 * ∑ j, symmetricFrameEigenvalues H hH (a j)) := by
  funext t
  exact tensorFrameEnergyCurve_eq_sum T H hH t

theorem tensorFrameEnergyCurve_differentiable {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) : Differentiable ℝ (tensorFrameEnergyCurve T H) := by
  rw [tensorFrameEnergyCurve_eq_weightedSum T H hH]
  exact fun t => (hasDerivAt_weightedExponentialSum _ _ _ t).differentiableAt

theorem tensorFrameEnergyCurve_deriv_differentiable {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    Differentiable ℝ (deriv (tensorFrameEnergyCurve T H)) := by
  rw [tensorFrameEnergyCurve_eq_weightedSum T H hH]
  exact fun t => (hasDerivAt_deriv_weightedExponentialSum _ _ _ t).differentiableAt

theorem hasDerivAt_tensorFrameEnergyCurve_zero {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    HasDerivAt (tensorFrameEnergyCurve T H) (2 * tensorHSInner T (tensorSlotAction H T)) 0 := by
  rw [tensorFrameEnergyCurve_eq_weightedSum T H hH]
  convert hasDerivAt_weightedExponentialSum Finset.univ
    (fun a : Fin r → Fin 3 => (tensorCoordinates (tensorFramePullback T
      (symmetricFrameEigenbasis H hH : Matrix (Fin 3) (Fin 3) ℝ)) a) ^ 2)
    (fun a => 2 * ∑ j, symmetricFrameEigenvalues H hH (a j)) 0 using 1
  rw [← tensorHSInner_orthogonal_frame T _ _ (real_unitary_mul_transpose (symmetricFrameEigenbasis H hH)),
    tensorSlotAction_pullback T H _ _ (symmetricFrame_eigenbasis_intertwines H hH)]
  simp only [tensorHSInner, tensorSlotAction_diagonal_coordinates, weightedExponentialSum,
    zero_mul, Real.exp_zero, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem tensorFrameEnergyCurve_first_derivative_zero {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    deriv (tensorFrameEnergyCurve T H) 0 = 2 * tensorHSInner T (tensorSlotAction H T) :=
  (hasDerivAt_tensorFrameEnergyCurve_zero T H hH).deriv

theorem tensorFrameEnergyCurve_second_derivative_zero {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    deriv (deriv (tensorFrameEnergyCurve T H)) 0 = 4 * (tensorHSNorm (tensorSlotAction H T)) ^ 2 := by
  simpa only [tensorFrameEnergyCurve] using
    tensorFramePullback_exp_norm_sq_second_derivative_original T H hH

theorem affineJet_energyCurve_eq {k r : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B H : Matrix (Fin 3) (Fin 3) ℝ) :
    (fun t : ℝ => (jetTensorHSNorm F c (B * NormedSpace.exp ℝ (t • H)) r) ^ 2) =
      tensorFrameEnergyCurve (affineJetTensor F c B r) H := by
  funext t
  rw [← tensorHSNorm_affineJetTensor, affineJetTensor_mul_frame]
  rfl

theorem hasDerivAt_jetTensorHSNorm_sq_frame_zero {k r : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    HasDerivAt (fun t : ℝ => (jetTensorHSNorm F c (B * NormedSpace.exp ℝ (t • H)) r) ^ 2)
      (2 * tensorHSInner (affineJetTensor F c B r) (tensorSlotAction H (affineJetTensor F c B r))) 0 := by
  rw [affineJet_energyCurve_eq]
  exact hasDerivAt_tensorFrameEnergyCurve_zero _ H hH

theorem jetTensorHSNorm_sq_frame_second_derivative_zero {k r : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    deriv (deriv (fun t : ℝ => (jetTensorHSNorm F c (B * NormedSpace.exp ℝ (t • H)) r) ^ 2)) 0 =
      4 * (tensorHSNorm (tensorSlotAction H (affineJetTensor F c B r))) ^ 2 := by
  rw [affineJet_energyCurve_eq]
  exact tensorFrameEnergyCurve_second_derivative_zero _ H hH

end PaperI
