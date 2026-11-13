import PaperILean.OriginalGaussShearThird
import PaperILean.OriginalNormalPhaseJetBounds

/-! I1303-I1305: relate the literal coordinate partials to the proved graph
operator norms. The order of all nested Frechet derivatives is explicit. -/
set_option maxSynthPendingDepth 4
noncomputable section
namespace PaperI
open Filter
open scoped Topology

theorem originalGauss_basis_norm (i : Fin 2) :
    ‖(if i=0 then ![1,0] else ![0,1] : Fin 2 → ℝ)‖ = 1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro j
    fin_cases i <;> fin_cases j <;> norm_num
  · have h := norm_le_pi_norm (if i=0 then ![1,0] else ![0,1] : Fin 2 → ℝ) i
    fin_cases i <;> simpa using h

theorem originalGauss_second_partial_bound (c : (Fin 2 → ℝ) → ℝ)
    (v e u : Fin 2 → ℝ) (hc : ContDiffAt ℝ 2 c v) :
    |fderiv ℝ (fun w => fderiv ℝ c w e) v u| ≤
      ‖fderiv ℝ (fderiv ℝ c) v‖ * ‖u‖ * ‖e‖ := by
  rw [originalGauss_partial_fderiv c v e u hc]
  calc
    _ ≤ ‖(fderiv ℝ (fderiv ℝ c) v) u‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg e)

theorem originalGauss_second_components_bound (c : (Fin 2 → ℝ) → ℝ)
    (v : Fin 2 → ℝ) (hc : ContDiffAt ℝ 2 c v) (H : ℝ)
    (hb : ‖fderiv ℝ (fderiv ℝ c) v‖ ≤ H) :
    |originalGaussR c v| ≤ H ∧ |originalGaussS c v| ≤ H ∧ |originalGaussT c v| ≤ H := by
  have he : ‖(![1,0] : Fin 2 → ℝ)‖=1 := originalGauss_basis_norm 0
  have hf : ‖(![0,1] : Fin 2 → ℝ)‖=1 := originalGauss_basis_norm 1
  refine ⟨?_,?_,?_⟩
  · have h := originalGauss_second_partial_bound c v ![1,0] ![1,0] hc
    simp only [he,mul_one] at h
    exact h.trans hb
  · have h := originalGauss_second_partial_bound c v ![1,0] ![0,1] hc
    simp only [he,hf,mul_one] at h
    exact h.trans hb
  · have h := originalGauss_second_partial_bound c v ![0,1] ![0,1] hc
    simp only [hf,mul_one] at h
    exact h.trans hb

theorem originalGauss_third_partial_eq (c : (Fin 2 → ℝ) → ℝ)
    (v e w u : Fin 2 → ℝ) (hc : ContDiffAt ℝ 3 c v) :
    fderiv ℝ (fun t => fderiv ℝ (fun s => fderiv ℝ c s e) t w) v u =
      fderiv ℝ (fderiv ℝ (fderiv ℝ c)) v u w e := by
  have he : (fun t => fderiv ℝ (fun s => fderiv ℝ c s e) t w) =ᶠ[𝓝 v]
      (fun t => fderiv ℝ (fderiv ℝ c) t w e) := by
    filter_upwards [hc.eventually (by norm_num)] with t ht
    exact originalGauss_partial_fderiv c t e w (ht.of_le (by decide))
  rw [he.fderiv_eq]
  exact originalNormal_second_apply_fderiv c v e w u hc

theorem originalGauss_third_partial_bound (c : (Fin 2 → ℝ) → ℝ)
    (v e w u : Fin 2 → ℝ) (hc : ContDiffAt ℝ 3 c v) :
    |fderiv ℝ (fun t => fderiv ℝ (fun s => fderiv ℝ c s e) t w) v u| ≤
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) v‖ * ‖u‖ * ‖w‖ * ‖e‖ := by
  rw [originalGauss_third_partial_eq c v e w u hc]
  exact originalNormal_trilinear_norm _ _ _ _

theorem originalGauss_third_components_bound (c : (Fin 2 → ℝ) → ℝ)
    (v : Fin 2 → ℝ) (hc : ContDiffAt ℝ 3 c v) (H : ℝ)
    (hb : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) v‖ ≤ H) :
    |fderiv ℝ (originalGaussR c) v ![1,0]| ≤ H ∧
    |fderiv ℝ (originalGaussS c) v ![1,0]| ≤ H ∧
    |fderiv ℝ (originalGaussS c) v ![0,1]| ≤ H := by
  have he : ‖(![1,0] : Fin 2 → ℝ)‖=1 := originalGauss_basis_norm 0
  have hf : ‖(![0,1] : Fin 2 → ℝ)‖=1 := originalGauss_basis_norm 1
  refine ⟨?_,?_,?_⟩
  · have h := originalGauss_third_partial_bound c v ![1,0] ![1,0] ![1,0] hc
    simp only [he,hf,mul_one] at h
    exact h.trans hb
  · have h := originalGauss_third_partial_bound c v ![1,0] ![0,1] ![1,0] hc
    simp only [he,hf,mul_one] at h
    exact h.trans hb
  · have h := originalGauss_third_partial_bound c v ![1,0] ![0,1] ![0,1] hc
    simp only [he,hf,mul_one] at h
    exact h.trans hb

end PaperI
