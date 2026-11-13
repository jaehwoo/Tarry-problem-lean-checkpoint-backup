import PaperILean.TensorFrameBounds
import PaperILean.BoundedJetCenterVariation
import PaperILean.MatrixLogEnergyModel

/-! Exact right-orthogonal invariance for full ordered-component HS norms.
All tensor orders are retained, including zero. No invertibility is required
of the initial frame. The positive-determinant domain is imposed separately. -/

noncomputable section
open scoped BigOperators Matrix
namespace PaperI

theorem sum_sq_orthogonal_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Q * Qᵀ = 1) (v : ι → ℝ) :
    (∑ j, (∑ i, Q i j * v i) ^ 2) = ∑ i, (v i) ^ 2 := by
  classical
  have rows (i l : ι) : (∑ j, Q i j * Q l j) = if i = l then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun M : Matrix ι ι ℝ => M i l) hQ
  calc
    (∑ j, (∑ i, Q i j * v i) ^ 2) =
        ∑ j, ∑ i, ∑ l, (Q i j * Q l j) * (v i * v l) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ∑ i, ∑ l, (∑ j, Q i j * Q l j) * (v i * v l) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = ∑ i, (v i) ^ 2 := by simp [rows, pow_two]

def tensorFrameMatrix (r : ℕ) (Q : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin r → Fin 3) (Fin r → Fin 3) ℝ :=
  fun a b => ∏ j, Q (a j) (b j)

theorem tensorFrameMatrix_orthogonal (r : ℕ)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q * Qᵀ = 1) :
    tensorFrameMatrix r Q * (tensorFrameMatrix r Q)ᵀ = 1 := by
  classical
  have rows (i l : Fin 3) : (∑ j, Q i j * Q l j) = if i = l then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i l) hQ
  ext a c
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tensorFrameMatrix]
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : Fin r) (b : Fin 3) => Q (a j) b * Q (c j) b)]
  simp only [rows, Matrix.one_apply]
  by_cases h : a = c
  · subst c
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem tensorCoordinates_frame_matrix {r : ℕ} (T : TensorSpace r)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin r → Fin 3) :
    tensorCoordinates (T.compContinuousLinearMap (fun _ => frameLinearMap Q)) b =
      ∑ a, tensorFrameMatrix r Q a b * tensorCoordinates T a := by
  unfold tensorCoordinates
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, frameLinearMap_apply]
  rw [tensor_expand_coordinates]
  simp only [Matrix.mulVec_single_one, Matrix.transpose_apply, tensorFrameMatrix]

theorem tensorHSNorm_orthogonal_frame {r : ℕ} (T : TensorSpace r)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q * Qᵀ = 1) :
    tensorHSNorm (T.compContinuousLinearMap (fun _ => frameLinearMap Q)) =
      tensorHSNorm T := by
  have hsq : (tensorHSNorm (T.compContinuousLinearMap (fun _ => frameLinearMap Q))) ^ 2 =
      (tensorHSNorm T) ^ 2 := by
    simp only [tensorHSNorm_sq, tensorCoordinates_frame_matrix]
    exact sum_sq_orthogonal_rows _ (tensorFrameMatrix_orthogonal r Q hQ) _
  nlinarith [tensorHSNorm_nonneg T,
    tensorHSNorm_nonneg (T.compContinuousLinearMap (fun _ => frameLinearMap Q))]

theorem affineJetTensor_mul_frame {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B Q : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) :
    affineJetTensor F c (B * Q) r =
      (affineJetTensor F c B r).compContinuousLinearMap (fun _ => frameLinearMap Q) := by
  ext v
  simp only [affineJetTensor_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    frameLinearMap_apply, Matrix.mulVec_mulVec]

theorem jetTensorHSNorm_right_orthogonal {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : Q * Qᵀ = 1) (r : ℕ) :
    jetTensorHSNorm F c (B * Q) r = jetTensorHSNorm F c B r := by
  rw [← tensorHSNorm_affineJetTensor, ← tensorHSNorm_affineJetTensor,
    affineJetTensor_mul_frame, tensorHSNorm_orthogonal_frame _ Q hQ]

theorem matrixFullHSNorm_right_orthogonal {n : ℕ}
    (B Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q * Qᵀ = 1) :
    matrixFullHSNorm (B * Q) = matrixFullHSNorm B := by
  have hsq : (matrixFullHSNorm (B * Q)) ^ 2 = (matrixFullHSNorm B) ^ 2 := by
    simp only [matrixFullHSNorm_sq, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [mul_comm] using sum_sq_orthogonal_rows Q hQ (B i)
  nlinarith [matrixFullHSNorm_nonneg (B * Q), matrixFullHSNorm_nonneg B]

end PaperI
