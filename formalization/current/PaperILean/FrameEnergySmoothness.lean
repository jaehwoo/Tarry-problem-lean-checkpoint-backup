import PaperILean.SymmetricLogSmoothness
import PaperILean.FrameEnergyContinuity
import PaperILean.TensorExponentialSums

/-! Actual full-energy smoothness in the frame variable on det B > 0.
F and c are fixed here; joint parameter smoothness is a separate obligation. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem contDiff_matrix_entry {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ⊤ (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff

theorem contDiff_matrixFullHSNorm_sq {n : ℕ} :
    ContDiff ℝ ⊤ (fun A : Matrix (Fin n) (Fin n) ℝ => (matrixFullHSNorm A) ^ 2) := by
  simp only [matrixFullHSNorm_sq]
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => (contDiff_matrix_entry i j).pow 2))

theorem contDiff_jetTensorComponent_frame {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (r : ℕ) (a : Fin r → Fin 3) :
    ContDiff ℝ ⊤ (fun B : Matrix (Fin 3) (Fin 3) ℝ => jetTensorComponent F c B r a) := by
  unfold jetTensorComponent
  apply (iteratedFDeriv ℝ r (phase F) c).contDiff.comp
  simp only [Matrix.mulVec_single_one]
  exact contDiff_pi.mpr (fun j => contDiff_pi.mpr (fun i => contDiff_matrix_entry i (a j)))

theorem contDiff_jetTensorHSNorm_sq_frame {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (r : ℕ) :
    ContDiff ℝ ⊤ (fun B : Matrix (Fin 3) (Fin 3) ℝ => (jetTensorHSNorm F c B r) ^ 2) := by
  simp only [jetTensorHSNorm_sq]
  exact ContDiff.sum (fun a _ => (contDiff_jetTensorComponent_frame F c r a).pow 2)

theorem contDiff_symmetricFrameGram : ContDiff ℝ ⊤ symmetricFrameGram := by
  have ht : ContDiff ℝ ⊤ (fun B : Matrix (Fin 3) (Fin 3) ℝ => Bᵀ) :=
    (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℝ ℝ).toContinuousLinearEquiv.contDiff
  have h := (symmetricMatrixProjection 3).contDiff.comp (contDiff_id.mul ht)
  have he : (fun B : Matrix (Fin 3) (Fin 3) ℝ => symmetricMatrixProjection 3 (B * Bᵀ)) =
      symmetricFrameGram := by
    funext B
    exact symmetricMatrixProjection_of_symm _ (by
      simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose])
  simpa only [Function.comp_def, id_eq, he] using h

theorem contDiffAt_frameLogEnergy (B : PositiveFrame) :
    ContDiffAt ℝ ⊤ (fun C : Matrix (Fin 3) (Fin 3) ℝ => sourceMatrixLogEnergy (C * Cᵀ)) B.val :=
  (contDiffAt_symmetricLogEnergy (symmetricFrameGram B.val) (positiveFrame_gram_posDef B)).comp
    B.val contDiff_symmetricFrameGram.contDiffAt

theorem contDiff_matrix_det_three :
    ContDiff ℝ ⊤ (Matrix.det : Matrix (Fin 3) (Fin 3) ℝ → ℝ) := by
  have he := contDiff_matrix_entry (n := 3)
  change ContDiff ℝ ⊤ (fun A : Matrix (Fin 3) (Fin 3) ℝ => A.det)
  simp only [Matrix.det_fin_three]
  exact ((((((he 0 0).mul (he 1 1)).mul (he 2 2)).sub
    (((he 0 0).mul (he 1 2)).mul (he 2 1))).sub
      (((he 0 1).mul (he 1 0)).mul (he 2 2))).add
        (((he 0 1).mul (he 1 2)).mul (he 2 0))).add
          (((he 0 2).mul (he 1 0)).mul (he 2 1)) |>.sub
            (((he 0 2).mul (he 1 1)).mul (he 2 0))

theorem contDiffAt_FrameEnergy {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) :
    ContDiffAt ℝ ⊤ (FrameEnergy F c lam) B.val := by
  unfold FrameEnergy
  exact ((contDiff_matrixFullHSNorm_sq.contDiffAt.add
    (ContDiff.sum (fun r _ => contDiff_jetTensorHSNorm_sq_frame F c r)).contDiffAt).sub
      (contDiffAt_const.mul (contDiff_matrix_det_three.contDiffAt.log B.property.ne'))).add
        (contDiffAt_const.mul (contDiffAt_frameLogEnergy B))

end PaperI
