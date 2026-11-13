import PaperILean.RotationTangentCoordinates
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! I331 prerequisite: the absolute determinant of left-trivialized tangent
coordinates. Its positivity and fixed-core bounds are not yet Haar-density
comparisons; the actual measure identification remains separate. -/
noncomputable section
open Set Filter
open scoped Topology Matrix Matrix.L2OpNorm BigOperators
namespace PaperI

def rotationChartSignedJacobian (x : PhysicalSpace) : ℝ :=
  (rotationTangentCoordinates x).toLinearMap.det

def rotationChartJacobian (x : PhysicalSpace) : ℝ := |rotationChartSignedJacobian x|

theorem rotationChartSignedJacobian_ne_zero (x : PhysicalSpace)
    (hx : x ∈ rotationChartSource) : rotationChartSignedJacobian x ≠ 0 := by
  intro h
  have hb := LinearMap.bot_lt_ker_of_det_eq_zero h
  rw [LinearMap.ker_eq_bot.mpr (rotationTangentCoordinates_injective x hx)] at hb
  exact lt_irrefl _ hb

theorem rotationChartJacobian_pos (x : PhysicalSpace) (hx : x ∈ rotationChartSource) :
    0 < rotationChartJacobian x := abs_pos.mpr (rotationChartSignedJacobian_ne_zero x hx)

theorem rotationChartJacobian_nonneg (x : PhysicalSpace) : 0 ≤ rotationChartJacobian x :=
  abs_nonneg _

theorem rotationChartSignedJacobian_continuous : Continuous rotationChartSignedJacobian :=
  ContinuousLinearMap.continuous_det.comp rotationTangentCoordinates_continuous

theorem rotationChartJacobian_continuous : Continuous rotationChartJacobian :=
  rotationChartSignedJacobian_continuous.abs

theorem rotationChartDifferential_contDiff : ContDiff ℝ ⊤ rotationChartDifferential := by
  have he : (fderiv ℝ (fun x => rotationMatrix (rotationCoordinateExp x))) =
      rotationChartDifferential := funext rotationCoordinateExp_matrix_fderiv
  simpa only [he] using
    rotationCoordinateExp_matrix_contDiff.fderiv_right (m := ⊤) (by simp)

theorem rotationTangentCoordinates_contDiff : ContDiff ℝ ⊤ rotationTangentCoordinates := by
  have hL : ContDiff ℝ ⊤ (fun x => rotationLeftMultiply (rotationCoordinateExp x)⁻¹) := by
    simp only [rotationLeftMultiply, rotationMatrix_inv]
    exact (ContinuousLinearMap.mul ℝ (Matrix (Fin 3) (Fin 3) ℝ)).contDiff.comp
      ((Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℝ ℝ).toContinuousLinearEquiv.contDiff.comp
        rotationCoordinateExp_matrix_contDiff)
  exact contDiff_const.clm_comp (hL.clm_comp rotationChartDifferential_contDiff)

theorem rotationChartSignedJacobian_contDiff : ContDiff ℝ ⊤ rotationChartSignedJacobian := by
  unfold rotationChartSignedJacobian
  simp_rw [← LinearMap.det_toMatrix', Matrix.det_apply', LinearMap.toMatrix'_apply]
  apply ContDiff.sum
  intro σ hσ
  apply contDiff_const.mul
  apply contDiff_prod
  intro i hi
  exact (ContinuousLinearMap.proj (σ i)).contDiff.comp
    (rotationTangentCoordinates_contDiff.clm_apply contDiff_const)

theorem rotationChartJacobian_contDiffAt (x : PhysicalSpace)
    (hx : x ∈ rotationChartSource) : ContDiffAt ℝ ⊤ rotationChartJacobian x := by
  rcases lt_or_gt_of_ne (rotationChartSignedJacobian_ne_zero x hx) with hn | hp
  · apply rotationChartSignedJacobian_contDiff.neg.contDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt rotationChartSignedJacobian_continuous continuous_const).mem_nhds hn]
      with y hy
    exact abs_of_neg hy
  · apply rotationChartSignedJacobian_contDiff.contDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const rotationChartSignedJacobian_continuous).mem_nhds hp]
      with y hy
    exact abs_of_pos hy

theorem rotationChartJacobian_contDiffOn : ContDiffOn ℝ ⊤ rotationChartJacobian rotationChartSource :=
  fun x hx => (rotationChartJacobian_contDiffAt x hx).contDiffWithinAt

theorem rotationChartSignedJacobian_zero : rotationChartSignedJacobian 0 = 1 := by
  simp only [rotationChartSignedJacobian, rotationTangentCoordinates_zero,
    ContinuousLinearMap.coe_id, LinearMap.det_id]

theorem rotationChartJacobian_zero : rotationChartJacobian 0 = 1 := by
  simp only [rotationChartJacobian, rotationChartSignedJacobian_zero, abs_one]

theorem zero_mem_rotationChartCore : (0 : PhysicalSpace) ∈ rotationChartCore := by
  change ‖skewMatrixOfCoordinates 0‖ ≤ 1/3
  rw [skewMatrixOfCoordinates_zero, norm_zero]
  norm_num

theorem rotationChartJacobian_uniform_bounds :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ x ∈ rotationChartCore,
      c ≤ rotationChartJacobian x ∧ rotationChartJacobian x ≤ C := by
  obtain ⟨a, ha, hmin⟩ := rotationChartCore_isCompact.exists_isMinOn
    ⟨0, zero_mem_rotationChartCore⟩ rotationChartJacobian_continuous.continuousOn
  obtain ⟨b, hb, hmax⟩ := rotationChartCore_isCompact.exists_isMaxOn
    ⟨0, zero_mem_rotationChartCore⟩ rotationChartJacobian_continuous.continuousOn
  exact ⟨rotationChartJacobian a, rotationChartJacobian b,
    rotationChartJacobian_pos a (rotationChartCore_subset_source ha), hmin hb,
    fun x hx => ⟨hmin hx, hmax hx⟩⟩

theorem rotationChartJacobian_uniform_source_bounds :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ (e : Fin 3 → ℝ), (∀ i, 0 < e i) →
      ∀ t : ℝ, t < 1/10 → ∀ x ∈ skewCoordinateBall e ((10/9)*t),
        c ≤ rotationChartJacobian x ∧ rotationChartJacobian x ≤ C := by
  obtain ⟨c, C, hc, hcC, h⟩ := rotationChartJacobian_uniform_bounds
  exact ⟨c, C, hc, hcC, fun e he t ht x hx =>
    h x (skewCoordinateBall_subset_chartCore e he t ht hx)⟩

theorem rotationChartJacobian_uniform_rotation_bounds :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i),
      ∀ t : ℝ, t < 1/10 → ∀ O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t,
        c ≤ rotationChartJacobian (rotationCoordinateLog O) ∧
          rotationChartJacobian (rotationCoordinateLog O) ≤ C := by
  obtain ⟨c, C, hc, hcC, h⟩ := rotationChartJacobian_uniform_bounds
  exact ⟨c, C, hc, hcC, fun e he t ht O hO =>
    h _ (rotationCoordinateLog_neighborhood_mem_chartCore e he t ht O hO)⟩

end PaperI
