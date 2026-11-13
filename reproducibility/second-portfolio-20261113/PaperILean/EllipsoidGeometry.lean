import PaperILean.MinimizingFrameComparison
import Mathlib.Topology.MetricSpace.Thickening

/-! Source278/298: actual open and closed Euclidean ellipsoid sets.
The two conventions are separate. Dilation is the image by v -> c+r*(B v),
including r=0 and negative r. PhysicalSpace keeps its existing coordinates. -/
noncomputable section
open Set
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

def physicalUnitBall : Set PhysicalSpace := {v | physicalEuclideanNorm v < 1}
def physicalClosedUnitBall : Set PhysicalSpace := {v | physicalEuclideanNorm v ≤ 1}
def frameBall (c : PhysicalSpace) (r : ℝ) (B : Matrix (Fin 3) (Fin 3) ℝ) : Set PhysicalSpace :=
  (fun v => c + r • (B *ᵥ v)) '' physicalUnitBall
def frameClosedBall (c : PhysicalSpace) (r : ℝ) (B : Matrix (Fin 3) (Fin 3) ℝ) : Set PhysicalSpace :=
  (fun v => c + r • (B *ᵥ v)) '' physicalClosedUnitBall

theorem physicalEuclideanNorm_zero : physicalEuclideanNorm (0 : PhysicalSpace) = 0 := by
  simp [physicalEuclideanNorm, coordinateL2Norm]

theorem physicalEuclideanNorm_smul (r : ℝ) (v : PhysicalSpace) :
    physicalEuclideanNorm (r • v) = |r| * physicalEuclideanNorm v := coordinateL2Norm_smul r v

theorem physical_abs_apply_le (v : PhysicalSpace) (i : Fin 3) :
    |v i| ≤ physicalEuclideanNorm v := by
  simpa only [physicalEuclideanNorm, coordinateL2Norm_eq_norm, Real.norm_eq_abs] using
    PiLp.norm_apply_le ((WithLp.linearEquiv 2 ℝ PhysicalSpace).symm v) i

theorem physical_pi_norm_le (v : PhysicalSpace) : ‖v‖ ≤ physicalEuclideanNorm v := by
  apply (pi_norm_le_iff_of_nonneg (physicalEuclideanNorm_nonneg v)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using physical_abs_apply_le v i

theorem frameBall_zero (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    frameBall c 0 B = {c} := by
  have hne : physicalUnitBall.Nonempty := ⟨0, by simp [physicalUnitBall, physicalEuclideanNorm_zero]⟩
  simp [frameBall, hne]

theorem frameClosedBall_zero (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    frameClosedBall c 0 B = {c} := by
  have hne : physicalClosedUnitBall.Nonempty := ⟨0, by simp [physicalClosedUnitBall, physicalEuclideanNorm_zero]⟩
  simp [frameClosedBall, hne]

theorem frameBall_subset_closed (c : PhysicalSpace) (r : ℝ) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    frameBall c r B ⊆ frameClosedBall c r B := by
  apply image_mono
  intro v hv
  exact (show physicalEuclideanNorm v < 1 from hv).le

theorem frameClosedBall_normalized_displacement (c : PhysicalSpace) (r : ℝ)
    (B : PositiveFrame) {x : PhysicalSpace} (hx : x ∈ frameClosedBall c r B.val) :
    physicalEuclideanNorm (B.val⁻¹ *ᵥ (x - c)) ≤ |r| := by
  obtain ⟨v, hv, rfl⟩ := hx
  simp only [add_sub_cancel_left, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    relativeFrame_initial, Matrix.one_mulVec, physicalEuclideanNorm_smul]
  exact mul_le_of_le_one_right (abs_nonneg r) hv

theorem frameClosedBall_physical_displacement (c : PhysicalSpace) (r : ℝ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : ‖B‖ ≤ 1)
    {x : PhysicalSpace} (hx : x ∈ frameClosedBall c r B) :
    physicalEuclideanNorm (x - c) ≤ |r| := by
  obtain ⟨v, hv, rfl⟩ := hx
  simp only [add_sub_cancel_left, physicalEuclideanNorm_smul]
  have hb := physicalEuclideanNorm_mulVec_le_opNorm B v
  have hnorm : physicalEuclideanNorm (B *ᵥ v) ≤ 1 := by
    calc
      _ ≤ ‖B‖ * physicalEuclideanNorm v := hb
      _ ≤ 1 * 1 := mul_le_mul hB hv (physicalEuclideanNorm_nonneg v) zero_le_one
      _ = 1 := by ring
  exact mul_le_of_le_one_right (abs_nonneg r) hnorm

theorem frameClosedBall_subset_cthickening (X : Set PhysicalSpace) {c : PhysicalSpace}
    (hc : c ∈ X) (r d : ℝ) (hr : |r| ≤ d) (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : ‖B‖ ≤ 1) :
    frameClosedBall c r B ⊆ Metric.cthickening d X := by
  intro x hx
  apply Metric.mem_cthickening_of_dist_le x c d X hc
  rw [dist_eq_norm]
  exact (physical_pi_norm_le _).trans ((frameClosedBall_physical_displacement c r B hB hx).trans hr)

end PaperI
