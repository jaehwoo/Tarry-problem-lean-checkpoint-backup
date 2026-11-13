import PaperILean.TensorPairingDerivative
import PaperILean.LinearNonautonomousODE
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! The original tensor-operator exponential identity at manuscript I284.
The identity is proved by the actual all-slot derivative and uniqueness of the
constant-coefficient tensor ODE. Symmetry is used only for the HS second variation.
All tensor orders, including zero, and arbitrary tensors are retained. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

local instance (r : ℕ) : NormedRing (TensorSpace r →L[ℝ] TensorSpace r) :=
  ContinuousLinearMap.toNormedRing
local instance (r : ℕ) : NormedAlgebra ℝ (TensorSpace r →L[ℝ] TensorSpace r) :=
  ContinuousLinearMap.toNormedAlgebra

private def originalFrameLinearMapL :
    Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (PhysicalSpace →L[ℝ] PhysicalSpace) :=
  LinearMap.toContinuousLinearMap {
    toFun := frameLinearMap
    map_add' := by
      intro A B
      ext v i
      simp [frameLinearMap_apply, Matrix.add_mulVec]
    map_smul' := by
      intro a A
      ext v i
      simp [frameLinearMap_apply, Matrix.smul_mulVec_assoc] }

private theorem original_hasDerivAt_frameLinearMap_exp
    (H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => frameLinearMap (NormedSpace.exp ℝ (s • H)))
      (frameLinearMap (NormedSpace.exp ℝ (t • H) * H)) t :=
  originalFrameLinearMapL.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const H t)

theorem hasDerivAt_tensorFramePullback_exp {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => tensorFramePullback T (NormedSpace.exp ℝ (s • H)))
      (tensorSlotAction H (tensorFramePullback T (NormedSpace.exp ℝ (t • H)))) t := by
  let M : ContinuousMultilinearMap ℝ (fun _ : Fin r => PhysicalSpace →L[ℝ] PhysicalSpace)
      (TensorSpace r →L[ℝ] TensorSpace r) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    ℝ (fun _ : Fin r => PhysicalSpace) (fun _ : Fin r => PhysicalSpace) ℝ
  have hf : HasDerivAt
      (fun s : ℝ => fun _ : Fin r => frameLinearMap (NormedSpace.exp ℝ (s • H)))
      (fun _ : Fin r => frameLinearMap (NormedSpace.exp ℝ (t • H) * H)) t :=
    hasDerivAt_pi.mpr (fun _ => original_hasDerivAt_frameLinearMap_exp H t)
  have hd := ((M.hasFDerivAt _).comp_hasDerivAt t hf).clm_apply (hasDerivAt_const t T)
  have he : (M.linearDeriv
        (fun _ : Fin r => frameLinearMap (NormedSpace.exp ℝ (t • H)))
        (fun _ : Fin r => frameLinearMap (NormedSpace.exp ℝ (t • H) * H))) T =
      tensorSlotAction H (tensorFramePullback T (NormedSpace.exp ℝ (t • H))) := by
    ext v
    simp only [ContinuousMultilinearMap.linearDeriv_apply,
      ContinuousLinearMap.sum_apply, ContinuousMultilinearMap.sum_apply,
      tensorSlotAction_apply]
    apply Finset.sum_congr rfl
    intro j _
    change T (fun i => (Function.update
      (fun _ : Fin r => frameLinearMap (NormedSpace.exp ℝ (t • H))) j
      (frameLinearMap (NormedSpace.exp ℝ (t • H) * H))) i (v i)) =
      T (fun i => NormedSpace.exp ℝ (t • H) *ᵥ
        (Function.update v j (H *ᵥ v j)) i)
    congr 1
    funext i
    by_cases hij : i = j
    · subst i
      simp only [Function.update_self, frameLinearMap_apply, Matrix.mulVec_mulVec]
    · simp only [Function.update_of_ne hij, frameLinearMap_apply]
  simpa only [map_zero, add_zero, he] using hd

theorem hasDerivAt_tensorOperator_exp {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp ℝ (s • tensorSlotActionCLM (r := r) H)) T)
      (tensorSlotAction H ((NormedSpace.exp ℝ (t • tensorSlotActionCLM (r := r) H)) T)) t := by
  have hd := (hasDerivAt_exp_smul_const' (tensorSlotActionCLM (r := r) H) t).clm_apply
    (hasDerivAt_const t T)
  simpa only [map_zero, add_zero, ContinuousLinearMap.mul_apply,
    tensorSlotActionCLM_apply] using hd

theorem tensorFramePullback_exp_eq_operator_exp {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    tensorFramePullback T (NormedSpace.exp ℝ (t • H)) =
      (NormedSpace.exp ℝ (t • tensorSlotActionCLM (r := r) H)) T := by
  have hzero : (0 : ℝ) ∈ Set.Ioo (-|t| - 1) (|t| + 1) := by
    constructor <;> linarith [abs_nonneg t]
  have ht : t ∈ Set.Ioo (-|t| - 1) (|t| + 1) := by
    constructor <;> linarith [le_abs_self t, neg_abs_le t]
  have hu := linearODE_unique_Ioo (fun _ : ℝ => tensorSlotActionCLM (r := r) H)
    continuous_const.continuousOn hzero
    (fun s _ => by simpa only [tensorSlotActionCLM_apply] using
      hasDerivAt_tensorFramePullback_exp T H s)
    (fun s _ => by simpa only [tensorSlotActionCLM_apply] using
      hasDerivAt_tensorOperator_exp T H s)
    (by simp only [zero_smul, NormedSpace.exp_zero, tensorFramePullback_one,
      ContinuousLinearMap.one_apply])
  exact hu ht

theorem hasDerivAt_tensorOperator_exp_norm_sq {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (tensorHSNorm ((NormedSpace.exp ℝ
      (s • tensorSlotActionCLM (r := r) H)) T)) ^ 2)
      (2 * tensorHSInner ((NormedSpace.exp ℝ (t • tensorSlotActionCLM (r := r) H)) T)
        (tensorSlotAction H ((NormedSpace.exp ℝ (t • tensorSlotActionCLM (r := r) H)) T))) t := by
  simpa only [tensorHSInner_comm] using
    hasDerivAt_tensorHSNorm_sq (hasDerivAt_tensorOperator_exp T H t)

theorem tensorOperator_exp_norm_sq_second_derivative_zero {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    deriv (deriv (fun t : ℝ => (tensorHSNorm
      ((NormedSpace.exp ℝ (t • tensorSlotActionCLM (r := r) H)) T)) ^ 2)) 0 =
      4 * (tensorHSNorm (tensorSlotAction H T)) ^ 2 := by
  have he : deriv (fun t : ℝ => (tensorHSNorm
      ((NormedSpace.exp ℝ (t • tensorSlotActionCLM (r := r) H)) T)) ^ 2) =
      fun t : ℝ => 2 * tensorHSInner ((NormedSpace.exp ℝ (t • tensorSlotActionCLM (r := r) H)) T)
        (tensorSlotAction H ((NormedSpace.exp ℝ (t • tensorSlotActionCLM (r := r) H)) T)) := by
    funext t
    exact (hasDerivAt_tensorOperator_exp_norm_sq T H t).deriv
  rw [he]
  have hd := (hasDerivAt_tensorHSInner_slot_self
    (hasDerivAt_tensorOperator_exp T H 0) H hH).const_mul 2
  have hh := hd.deriv
  simpa only [zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply,
    tensorHSInner_self, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using hh

theorem tensorFramePullback_exp_norm_sq_second_derivative_original {r : ℕ}
    (T : TensorSpace r) (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    deriv (deriv (fun t : ℝ => (tensorHSNorm
      (tensorFramePullback T (NormedSpace.exp ℝ (t • H)))) ^ 2)) 0 =
      4 * (tensorHSNorm (tensorSlotAction H T)) ^ 2 := by
  simp only [tensorFramePullback_exp_eq_operator_exp]
  exact tensorOperator_exp_norm_sq_second_derivative_zero T H hH

end PaperI
