import PaperILean.FrameEnergy
import PaperILean.MatrixTraceSquareDifferential

/-! Continuity of the actual full energy on det B > 0, for fixed F,c,lambda.
No regularity of a chosen minimizer is used. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem continuous_matrixFullHSNorm {n : ℕ} :
    Continuous (matrixFullHSNorm : Matrix (Fin n) (Fin n) ℝ → ℝ) := by
  unfold matrixFullHSNorm coordinateL2Norm
  fun_prop

theorem continuous_jetTensorComponent_frame {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (r : ℕ) (a : Fin r → Fin 3) :
    Continuous (fun B : Matrix (Fin 3) (Fin 3) ℝ => jetTensorComponent F c B r a) := by
  unfold jetTensorComponent
  apply (iteratedFDeriv ℝ r (phase F) c).cont.comp
  simp only [Matrix.mulVec_single_one]
  fun_prop

theorem continuous_jetTensorHSNorm_frame {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (r : ℕ) :
    Continuous (fun B : Matrix (Fin 3) (Fin 3) ℝ => jetTensorHSNorm F c B r) := by
  unfold jetTensorHSNorm
  exact Real.continuous_sqrt.comp (continuous_finset_sum _
    (fun a _ => (continuous_jetTensorComponent_frame F c r a).pow 2))

def symmetricFrameGram (B : Matrix (Fin 3) (Fin 3) ℝ) : SymmetricMatrix 3 :=
  symmetricMatrixOf (B * Bᵀ) (by
    show (B * Bᵀ)ᵀ = B * Bᵀ
    rw [Matrix.transpose_mul, Matrix.transpose_transpose])

theorem continuous_symmetricFrameGram : Continuous symmetricFrameGram := by
  apply Continuous.subtype_mk
  exact continuous_id.matrix_mul continuous_id.matrix_transpose

theorem continuousAt_frameLogEnergy (B : PositiveFrame) :
    ContinuousAt (fun C : Matrix (Fin 3) (Fin 3) ℝ => sourceMatrixLogEnergy (C * Cᵀ)) B.val := by
  exact (symmetricLogEnergy_posDef_hasFDerivAt (symmetricFrameGram B.val)
    (positiveFrame_gram_posDef B)).continuousAt.comp continuous_symmetricFrameGram.continuousAt

theorem continuousAt_FrameEnergy {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) :
    ContinuousAt (FrameEnergy F c lam) B.val := by
  unfold FrameEnergy
  apply ContinuousAt.add
  · apply ContinuousAt.sub
    · exact (continuous_matrixFullHSNorm.pow 2).continuousAt.add
        ((continuous_finset_sum _ (fun r _ => (continuous_jetTensorHSNorm_frame F c r).pow 2)).continuousAt)
    · exact continuousAt_const.mul (continuous_id.matrix_det.continuousAt.log B.property.ne')
  · exact continuousAt_const.mul (continuousAt_frameLogEnergy B)

theorem continuousOn_FrameEnergy {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) :
    ContinuousOn (FrameEnergy F c lam) {B : Matrix (Fin 3) (Fin 3) ℝ | 0 < B.det} := by
  intro B hB
  exact (continuousAt_FrameEnergy F c lam ⟨B, hB⟩).continuousWithinAt

end PaperI
