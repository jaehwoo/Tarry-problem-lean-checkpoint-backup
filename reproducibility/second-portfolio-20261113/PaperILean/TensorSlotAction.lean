import PaperILean.TensorContractionGram
import PaperILean.FrameExponentialSpectral

/-! The source slot action L_H on actual continuous multilinear tensors.
The HS pairing below uses every ordered coordinate, not the Pi operator norm. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def tensorHSInner {r : ℕ} (T S : TensorSpace r) : ℝ :=
  ∑ a : Fin r → Fin 3, tensorCoordinates T a * tensorCoordinates S a

theorem tensorHSInner_comm {r : ℕ} (T S : TensorSpace r) :
    tensorHSInner T S = tensorHSInner S T := by simp only [tensorHSInner, mul_comm]

theorem tensorHSInner_self {r : ℕ} (T : TensorSpace r) :
    tensorHSInner T T = (tensorHSNorm T) ^ 2 := by
  rw [tensorHSNorm_sq]
  simp only [tensorHSInner, pow_two]

theorem tensorHSNorm_add_sq {r : ℕ} (T S : TensorSpace r) :
    (tensorHSNorm (T + S)) ^ 2 =
      (tensorHSNorm T) ^ 2 + 2 * tensorHSInner T S + (tensorHSNorm S) ^ 2 := by
  simp only [tensorHSNorm_sq, tensorHSInner, tensorCoordinates,
    ContinuousMultilinearMap.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

def tensorFramePullback {r : ℕ} (T : TensorSpace r) (A : Matrix (Fin 3) (Fin 3) ℝ) : TensorSpace r :=
  T.compContinuousLinearMap (fun _ => frameLinearMap A)

theorem tensorFramePullback_apply {r : ℕ} (T : TensorSpace r)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin r → PhysicalSpace) :
    tensorFramePullback T A v = T (fun j => A *ᵥ v j) := rfl

theorem tensorFramePullback_add {r : ℕ} (T S : TensorSpace r) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    tensorFramePullback (T + S) A = tensorFramePullback T A + tensorFramePullback S A := by
  ext v
  rfl

theorem tensorFramePullback_mul {r : ℕ} (T : TensorSpace r)
    (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    tensorFramePullback (tensorFramePullback T A) B = tensorFramePullback T (A * B) := by
  ext v
  simp only [tensorFramePullback_apply, Matrix.mulVec_mulVec]

theorem tensorFramePullback_one {r : ℕ} (T : TensorSpace r) : tensorFramePullback T 1 = T := by
  ext v
  simp only [tensorFramePullback_apply, Matrix.one_mulVec]

theorem tensorHSInner_orthogonal_frame {r : ℕ} (T S : TensorSpace r)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q * Qᵀ = 1) :
    tensorHSInner (tensorFramePullback T Q) (tensorFramePullback S Q) = tensorHSInner T S := by
  have h := tensorHSNorm_add_sq (tensorFramePullback T Q) (tensorFramePullback S Q)
  rw [← tensorFramePullback_add] at h
  simp only [tensorFramePullback, tensorHSNorm_orthogonal_frame _ Q hQ] at h
  rw [tensorHSNorm_add_sq] at h
  change tensorHSInner (T.compContinuousLinearMap (fun _ => frameLinearMap Q))
    (S.compContinuousLinearMap (fun _ => frameLinearMap Q)) = tensorHSInner T S
  linarith

def tensorOneSlotAction {r : ℕ} (H : Matrix (Fin 3) (Fin 3) ℝ)
    (j : Fin r) (T : TensorSpace r) : TensorSpace r :=
  T.compContinuousLinearMap (fun i => if i = j then frameLinearMap H else ContinuousLinearMap.id ℝ PhysicalSpace)

def tensorSlotAction {r : ℕ} (H : Matrix (Fin 3) (Fin 3) ℝ) (T : TensorSpace r) : TensorSpace r :=
  ∑ j : Fin r, tensorOneSlotAction H j T

theorem tensorOneSlotAction_apply {r : ℕ} (H : Matrix (Fin 3) (Fin 3) ℝ)
    (j : Fin r) (T : TensorSpace r) (v : Fin r → PhysicalSpace) :
    tensorOneSlotAction H j T v = T (Function.update v j (H *ᵥ v j)) := by
  unfold tensorOneSlotAction
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  by_cases hi : i = j
  · subst i
    simp [frameLinearMap_apply]
  · simp [hi]

theorem tensorSlotAction_apply {r : ℕ} (H : Matrix (Fin 3) (Fin 3) ℝ)
    (T : TensorSpace r) (v : Fin r → PhysicalSpace) :
    tensorSlotAction H T v = ∑ j : Fin r, T (Function.update v j (H *ᵥ v j)) := by
  simp only [tensorSlotAction, ContinuousMultilinearMap.sum_apply, tensorOneSlotAction_apply]

theorem tensorSlotAction_order_zero (H : Matrix (Fin 3) (Fin 3) ℝ) (T : TensorSpace 0) :
    tensorSlotAction H T = 0 := by simp [tensorSlotAction]

theorem tensorSlotAction_zero_direction {r : ℕ} (T : TensorSpace r) : tensorSlotAction 0 T = 0 := by
  ext v
  simp only [tensorSlotAction_apply, Matrix.zero_mulVec, ContinuousMultilinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  exact T.map_coord_zero j (by simp)

end PaperI
