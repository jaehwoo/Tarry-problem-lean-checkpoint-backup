import PaperILean.AffineJetCenterDerivative
import PaperILean.TensorSlotSpectral

/-! Derivatives in the actual multilinear tensor space and the full ordered
HS pairing. The slot sum is bundled as a continuous linear map. Its abstract
operator exponential is not identified with frame pullback in this module.
-/
noncomputable section
open scoped BigOperators Matrix
namespace PaperI

def tensorEvaluationCLM {r : ℕ} (v : Fin r → PhysicalSpace) : TensorSpace r →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun T => T v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (∏ j, ‖v j‖) (fun T => (T.le_opNorm v).trans_eq (mul_comm _ _))

theorem hasDerivAt_tensor_apply {r : ℕ} {T : ℝ → TensorSpace r}
    {T' : TensorSpace r} {t : ℝ} (hT : HasDerivAt T T' t)
    (v : Fin r → PhysicalSpace) : HasDerivAt (fun s => T s v) (T' v) t :=
  (tensorEvaluationCLM v).hasFDerivAt.comp_hasDerivAt t hT

def tensorSlotActionCLM {r : ℕ} (H : Matrix (Fin 3) (Fin 3) ℝ) :
    TensorSpace r →L[ℝ] TensorSpace r :=
  ∑ j : Fin r, ContinuousMultilinearMap.compContinuousLinearMapL
    (fun i => if i = j then frameLinearMap H else ContinuousLinearMap.id ℝ PhysicalSpace)

theorem tensorSlotActionCLM_apply {r : ℕ} (H : Matrix (Fin 3) (Fin 3) ℝ)
    (T : TensorSpace r) : tensorSlotActionCLM H T = tensorSlotAction H T := by
  simp only [tensorSlotActionCLM, ContinuousLinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMapL_apply, tensorSlotAction, tensorOneSlotAction]

theorem hasDerivAt_tensorSlotAction {r : ℕ} {T : ℝ → TensorSpace r}
    {T' : TensorSpace r} {t : ℝ} (hT : HasDerivAt T T' t)
    (H : Matrix (Fin 3) (Fin 3) ℝ) :
    HasDerivAt (fun s => tensorSlotAction H (T s)) (tensorSlotAction H T') t := by
  simpa only [Function.comp_def, tensorSlotActionCLM_apply] using
    (tensorSlotActionCLM H).hasFDerivAt.comp_hasDerivAt t hT

theorem hasDerivAt_tensorHSInner {r : ℕ} {T S : ℝ → TensorSpace r}
    {T' S' : TensorSpace r} {t : ℝ} (hT : HasDerivAt T T' t) (hS : HasDerivAt S S' t) :
    HasDerivAt (fun s => tensorHSInner (T s) (S s))
      (tensorHSInner T' (S t) + tensorHSInner (T t) S') t := by
  simpa only [tensorHSInner, tensorCoordinates, Finset.sum_add_distrib] using
    HasDerivAt.sum (u := Finset.univ) (fun (a : Fin r → Fin 3) _ =>
      (hasDerivAt_tensor_apply hT (fun j => Pi.single (a j) 1)).mul
        (hasDerivAt_tensor_apply hS (fun j => Pi.single (a j) 1)))

theorem hasDerivAt_tensorHSNorm_sq {r : ℕ} {T : ℝ → TensorSpace r}
    {T' : TensorSpace r} {t : ℝ} (hT : HasDerivAt T T' t) :
    HasDerivAt (fun s => (tensorHSNorm (T s)) ^ 2)
      (2 * tensorHSInner T' (T t)) t := by
  have hh := hasDerivAt_tensorHSInner hT hT
  simpa only [tensorHSInner_self, tensorHSInner_comm (T t) T', two_mul] using hh

theorem hasDerivAt_tensorHSInner_slot_self {r : ℕ} {T : ℝ → TensorSpace r}
    {T' : TensorSpace r} {t : ℝ} (hT : HasDerivAt T T' t)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    HasDerivAt (fun s => tensorHSInner (T s) (tensorSlotAction H (T s)))
      (2 * tensorHSInner T' (tensorSlotAction H (T t))) t := by
  have hh := hasDerivAt_tensorHSInner hT (hasDerivAt_tensorSlotAction hT H)
  have he : tensorHSInner (T t) (tensorSlotAction H T') =
      tensorHSInner T' (tensorSlotAction H (T t)) := by
    rw [← tensorSlotAction_selfAdjoint H hH, tensorHSInner_comm]
  simpa only [he, two_mul] using hh

end PaperI
