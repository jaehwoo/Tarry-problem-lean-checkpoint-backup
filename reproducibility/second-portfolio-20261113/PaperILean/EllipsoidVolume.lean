import PaperILean.FrameComparisonComposition
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Source278/298: actual Lebesgue volume of ellipsoid sets and quantitative
comparison. The elementary determinant bound is deliberately nonoptimal;
only a fixed dimension-three constant is needed. All real dilations are kept. -/
noncomputable section
open Set MeasureTheory
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

theorem matrix_entry_abs_le_opNorm (A : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    |A i j| ≤ ‖A‖ := by
  have hn : physicalEuclideanNorm (Pi.single j (1 : ℝ)) = 1 := by
    simp [physicalEuclideanNorm, coordinateL2Norm, Pi.single_apply]
  have h := (physical_abs_apply_le (A *ᵥ Pi.single j 1) i).trans
    (physicalEuclideanNorm_mulVec_le_opNorm A (Pi.single j 1))
  simpa only [Matrix.mulVec_single_one, Matrix.transpose_apply, hn, mul_one] using h

theorem matrix_abs_det_le_six_mul_opNorm_cube (A : Matrix (Fin 3) (Fin 3) ℝ) :
    |A.det| ≤ 6 * ‖A‖ ^ 3 := by
  have hp (i j l m n p : Fin 3) : |A i j * A l m * A n p| ≤ ‖A‖ ^ 3 := by
    rw [abs_mul, abs_mul, pow_succ, pow_two]
    exact mul_le_mul (mul_le_mul (matrix_entry_abs_le_opNorm A i j)
      (matrix_entry_abs_le_opNorm A l m) (abs_nonneg _) (norm_nonneg _))
      (matrix_entry_abs_le_opNorm A n p) (abs_nonneg _) (mul_self_nonneg _)
  let a := A 0 0 * A 1 1 * A 2 2
  let b := A 0 0 * A 1 2 * A 2 1
  let c := A 0 1 * A 1 0 * A 2 2
  let d := A 0 1 * A 1 2 * A 2 0
  let e := A 0 2 * A 1 0 * A 2 1
  let f := A 0 2 * A 1 1 * A 2 0
  have hsum : |a - b - c + d + e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
    have h1 : |a - b| ≤ |a| + |b| := by simpa only [Real.norm_eq_abs] using norm_sub_le a b
    have h2 : |a - b - c| ≤ |a - b| + |c| := by simpa only [Real.norm_eq_abs] using norm_sub_le (a-b) c
    have h3 : |a - b - c + d + e - f| ≤ |a - b - c + d + e| + |f| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (a-b-c+d+e) f
    linarith [abs_add_le (a - b - c) d, abs_add_le (a - b - c + d) e]
  rw [Matrix.det_fin_three]
  exact hsum.trans (by
    dsimp [a,b,c,d,e,f]
    linarith [hp 0 0 1 1 2 2, hp 0 0 1 2 2 1, hp 0 1 1 0 2 2,
      hp 0 1 1 2 2 0, hp 0 2 1 0 2 1, hp 0 2 1 1 2 0])

theorem relativeFrame_det (B C : PositiveFrame) :
    (B.val⁻¹ * C.val).det = C.val.det / B.val.det := by
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  ring

theorem positiveFrame_det_le_of_relative_opNorm (B C : PositiveFrame) (L : ℝ)
    (h : ‖B.val⁻¹ * C.val‖ ≤ L) : C.val.det ≤ (6 * L ^ 3) * B.val.det := by
  have hd : 0 < (B.val⁻¹ * C.val).det := by rw [relativeFrame_det]; exact div_pos C.property B.property
  have hb := matrix_abs_det_le_six_mul_opNorm_cube (B.val⁻¹ * C.val)
  rw [abs_of_pos hd, relativeFrame_det] at hb
  have hc : C.val.det / B.val.det ≤ 6 * L ^ 3 :=
    hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 3) (by norm_num))
  exact (div_le_iff₀ B.property).mp hc

theorem frameImage_volume (c : PhysicalSpace) (r : ℝ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (U : Set PhysicalSpace) :
    volume ((fun v => c + r • (B *ᵥ v)) '' U) =
      ENNReal.ofReal (|r| ^ 3 * |B.det|) * volume U := by
  have hs : ((fun v => c + r • (B *ᵥ v)) '' U) =
      (fun v : PhysicalSpace => c + v) '' ((Matrix.toLin' (r • B)) '' U) := by
    rw [image_image]
    funext v
    simp only [Function.comp_apply, Matrix.toLin'_apply, Matrix.smul_mulVec_assoc]
  rw [hs, image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap,
    LinearMap.det_toLin', Matrix.det_smul]
  simp only [Fintype.card_fin, smul_eq_mul, abs_mul, abs_pow]

theorem frameBall_volume (c : PhysicalSpace) (r : ℝ) (B : PositiveFrame) :
    volume (frameBall c r B.val) =
      ENNReal.ofReal (|r| ^ 3 * B.val.det) * volume physicalUnitBall := by
  simpa only [frameBall, abs_of_pos B.property] using frameImage_volume c r B.val physicalUnitBall

theorem frameClosedBall_volume (c : PhysicalSpace) (r : ℝ) (B : PositiveFrame) :
    volume (frameClosedBall c r B.val) =
      ENNReal.ofReal (|r| ^ 3 * B.val.det) * volume physicalClosedUnitBall := by
  simpa only [frameClosedBall, abs_of_pos B.property] using frameImage_volume c r B.val physicalClosedUnitBall

theorem frameImage_volume_comparison (c d : PhysicalSpace) (r : ℝ) (B C : PositiveFrame)
    (U : Set PhysicalSpace) (V : ℝ) (hV : 0 ≤ V) (hdet : B.val.det ≤ V * C.val.det) :
    volume ((fun v => c + r • (B.val *ᵥ v)) '' U) ≤
      ENNReal.ofReal V * volume ((fun v => d + r • (C.val *ᵥ v)) '' U) := by
  rw [frameImage_volume, frameImage_volume, abs_of_pos B.property, abs_of_pos C.property]
  calc
    ENNReal.ofReal (|r| ^ 3 * B.val.det) * volume U ≤
        ENNReal.ofReal (|r| ^ 3 * (V * C.val.det)) * volume U :=
      mul_le_mul_right' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hdet (by positivity))) _
    _ = ENNReal.ofReal V * (ENNReal.ofReal (|r| ^ 3 * C.val.det) * volume U) := by
      rw [show |r| ^ 3 * (V * C.val.det) = V * (|r| ^ 3 * C.val.det) by ring,
        ENNReal.ofReal_mul hV, mul_assoc]

theorem frameBalls_volume_comparison (c d : PhysicalSpace) (r : ℝ) (B C : PositiveFrame)
    (V : ℝ) (hV : 0 ≤ V) (hdet : B.val.det ≤ V * C.val.det) :
    volume (frameBall c r B.val) ≤ ENNReal.ofReal V * volume (frameBall d r C.val) ∧
    volume (frameClosedBall c r B.val) ≤ ENNReal.ofReal V * volume (frameClosedBall d r C.val) :=
  ⟨frameImage_volume_comparison c d r B C physicalUnitBall V hV hdet,
    frameImage_volume_comparison c d r B C physicalClosedUnitBall V hV hdet⟩

theorem physicalMeasure_eq_volume : physicalMeasure = (volume : Measure PhysicalSpace) := rfl

theorem physicalUnitBall_volume_pos : 0 < volume physicalUnitBall := by
  have hc : Continuous physicalEuclideanNorm := by
    unfold physicalEuclideanNorm coordinateL2Norm
    fun_prop
  have ho : IsOpen physicalUnitBall := isOpen_lt hc continuous_const
  exact ho.measure_pos volume ⟨0, by simp [physicalUnitBall, physicalEuclideanNorm_zero]⟩

theorem physicalClosedUnitBall_volume_lt_top : volume physicalClosedUnitBall < ⊤ := by
  have hs : physicalClosedUnitBall ⊆ Metric.closedBall (0 : PhysicalSpace) 1 := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (physical_pi_norm_le v).trans hv
  exact (Metric.isBounded_closedBall.subset hs).measure_lt_top

theorem physical_unit_ball_volumes_positive_finite :
    0 < volume physicalUnitBall ∧ volume physicalUnitBall < ⊤ ∧
      0 < volume physicalClosedUnitBall ∧ volume physicalClosedUnitBall < ⊤ := by
  have hs : physicalUnitBall ⊆ physicalClosedUnitBall := fun _ h => (show _ < (1 : ℝ) from h).le
  exact ⟨physicalUnitBall_volume_pos,
    (measure_mono hs).trans_lt physicalClosedUnitBall_volume_lt_top,
    physicalUnitBall_volume_pos.trans_le (measure_mono hs), physicalClosedUnitBall_volume_lt_top⟩

theorem frameBalls_volume_positive_finite (c : PhysicalSpace) (r : ℝ) (hr : r ≠ 0)
    (B : PositiveFrame) :
    0 < volume (frameBall c r B.val) ∧ volume (frameBall c r B.val) < ⊤ ∧
      0 < volume (frameClosedBall c r B.val) ∧ volume (frameClosedBall c r B.val) < ⊤ := by
  have hscale : 0 < ENNReal.ofReal (|r| ^ 3 * B.val.det) :=
    ENNReal.ofReal_pos.mpr (mul_pos (pow_pos (abs_pos.mpr hr) 3) B.property)
  obtain ⟨ho, hfo, hc, hfc⟩ := physical_unit_ball_volumes_positive_finite
  rw [frameBall_volume, frameClosedBall_volume]
  exact ⟨ENNReal.mul_pos hscale.ne' ho.ne', ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfo,
    ENNReal.mul_pos hscale.ne' hc.ne', ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfc⟩

end PaperI
