import PaperILean.JointPolynomialSmoothness
import PaperILean.RawJetContractionBounds

/-! I286: the actual tensor-valued center derivative, with every raw factor
and frame slot retained. The frame can be singular and the direction zero.
The top-order statement uses the checked derivative-above-degree theorem.
-/
noncomputable section
open scoped BigOperators Matrix
namespace PaperI

theorem hasFDerivAt_iteratedFDeriv_phase {k : ℕ} (F : CoefficientSpace k)
    (r : ℕ) (c : PhysicalSpace) :
    HasFDerivAt (iteratedFDeriv ℝ r (phase F))
      (iteratedFDeriv ℝ (r + 1) (phase F) c).curryLeft c := by
  have hs : ContDiff ℝ ⊤ (iteratedFDeriv ℝ r (phase F)) :=
    (contDiff_iteratedFDeriv_phase_joint r).comp (contDiff_const.prodMk contDiff_id)
  exact (hs.differentiable (by simp)).differentiableAt.hasFDerivAt

theorem hasDerivAt_affineJetTensor_center {k : ℕ} (F : CoefficientSpace k)
    (r : ℕ) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (h : PhysicalSpace) (t : ℝ) :
    HasDerivAt (fun s : ℝ => affineJetTensor F (c + s • (B *ᵥ h)) B r)
      ((affineJetTensor F (c + t • (B *ᵥ h)) B (r + 1)).curryLeft h) t := by
  have hc : HasDerivAt (fun s : ℝ => c + s • (B *ᵥ h)) (B *ᵥ h) t := by
    simpa only [one_smul, zero_add] using
      (hasDerivAt_const t c).add ((hasDerivAt_id t).smul_const (B *ᵥ h))
  have hd := (hasFDerivAt_iteratedFDeriv_phase F r (c + t • (B *ᵥ h))).comp_hasDerivAt t hc
  have hp := (ContinuousMultilinearMap.compContinuousLinearMapL
    (G := ℝ) (fun _ : Fin r => frameLinearMap B)).hasFDerivAt.comp_hasDerivAt t hd
  simpa only [affineJetTensor, tensor_frame_curryLeft,
    ContinuousMultilinearMap.compContinuousLinearMapL_apply] using hp

theorem hasDerivAt_affineJetTensor_center_zero {k : ℕ} (F : CoefficientSpace k)
    (r : ℕ) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (h : PhysicalSpace) :
    HasDerivAt (fun t : ℝ => affineJetTensor F (c + t • (B *ᵥ h)) B r)
      ((affineJetTensor F c B (r + 1)).curryLeft h) 0 := by
  simpa only [zero_smul, add_zero] using hasDerivAt_affineJetTensor_center F r c B h 0

theorem hasDerivAt_affineJetTensor_center_top {k : ℕ} (F : CoefficientSpace k)
    (r : ℕ) (hr : k ≤ r) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (h : PhysicalSpace) (t : ℝ) :
    HasDerivAt (fun s : ℝ => affineJetTensor F (c + s • (B *ᵥ h)) B r) 0 t := by
  have hz := affineJetTensor_eq_zero_of_degree_lt F (c + t • (B *ᵥ h)) B (r + 1)
    (by omega)
  have he : (affineJetTensor F (c + t • (B *ᵥ h)) B (r + 1)).curryLeft h = 0 := by
    rw [hz]
    ext v
    rfl
  simpa only [he] using hasDerivAt_affineJetTensor_center F r c B h t

end PaperI
