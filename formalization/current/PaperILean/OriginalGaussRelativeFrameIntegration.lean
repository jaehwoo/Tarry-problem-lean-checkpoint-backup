import PaperILean.OriginalUpperIntegralBounds

/-! I1305: compose integration with the genuine original Gauss path and its
proved graph-jet body bound. A single M is required on the whole path. -/
set_option maxSynthPendingDepth 4
noncomputable section
namespace PaperI
open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem originalAffineBodyCoordinates_continuousOn
    (g v : ℝ → Fin 6 → ℝ) (S : Set ℝ)
    (hg : ContinuousOn g S) (hv : ContinuousOn v S) :
    ContinuousOn (fun t => originalAffineBodyCoordinates (g t) (v t)) S := by
  have hgi (i : Fin 6) : ContinuousOn (fun t => g t i) S := (continuous_apply i).comp_continuousOn hg
  have hvi (i : Fin 6) : ContinuousOn (fun t => v t i) S := (continuous_apply i).comp_continuousOn hv
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · exact hvi 0
  · exact (hvi 1).sub ((hgi 0).mul (hvi 3))
  · exact ((hvi 2).sub ((hgi 0).mul (hvi 4))).add
      (((hgi 0).mul (hgi 3) |>.sub (hgi 1)).mul (hvi 5))
  · exact hvi 3
  · exact (hvi 4).sub ((hgi 3).mul (hvi 5))
  · exact hvi 5

theorem originalGaussFrameVelocity_continuousWithinAt_path
    (c Y : (Fin 2 → ℝ) → ℝ) (q u : ℝ → Fin 2 → ℝ) (S : Set ℝ) (t : ℝ)
    (hq : ContinuousAt q t) (hu : ContinuousWithinAt u S t)
    (hc : ContDiffAt ℝ 3 c ![Y (q t), q t 1]) (hY : ContDiffAt ℝ 1 Y (q t))
    (hr : originalGaussR c ![Y (q t),q t 1] ≠ 0) :
    ContinuousWithinAt (fun s => originalGaussFrameVelocity c Y (q s) (u s)) S t := by
  have hbase : ContDiffAt ℝ 1 (fun a : Fin 2 → ℝ => (![Y a,a 1] : Fin 2 → ℝ)) (q t) := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact hY
    · exact (contDiff_apply ℝ ℝ 1).contDiffAt
  have hP : ContDiffAt ℝ 2 (originalGaussCy c) ![Y (q t),q t 1] :=
    (hc.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hR : ContDiffAt ℝ 1 (originalGaussR c) ![Y (q t),q t 1] :=
    (hP.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hS : ContDiffAt ℝ 1 (originalGaussS c) ![Y (q t),q t 1] :=
    (hP.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hQbase : ContDiffAt ℝ 1 (originalGaussCz c) ![Y (q t),q t 1] :=
    ((hc.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const).of_le (by norm_num)
  have hDbase : ContDiffAt ℝ 1 (originalGaussShear c) ![Y (q t),q t 1] := hS.neg.div hR hr
  have hQ : ContDiffAt ℝ 1 (fun a => originalGaussCz c ![Y a,a 1]) (q t) :=
    ContDiffAt.comp (g := originalGaussCz c) (f := fun a : Fin 2 → ℝ => (![Y a,a 1] : Fin 2 → ℝ)) (q t) hQbase hbase
  have hD : ContDiffAt ℝ 1 (fun a => originalGaussShear c ![Y a,a 1]) (q t) :=
    ContDiffAt.comp (g := originalGaussShear c) (f := fun a : Fin 2 → ℝ => (![Y a,a 1] : Fin 2 → ℝ)) (q t) hDbase hbase
  have hC : ContDiffAt ℝ 1 (fun a => c ![Y a,a 1]) (q t) :=
    (hc.of_le (by norm_num)).comp (q t) hbase
  have happ (f : ℝ → (Fin 2 → ℝ) →L[ℝ] ℝ) (hf : ContinuousAt f t) :
      ContinuousWithinAt (fun s => f s (u s)) S t :=
    isBoundedBilinearMap_apply.continuous.continuousAt.comp_continuousWithinAt
      (hf.continuousWithinAt.prodMk hu)
  have hdQ := happ _ ((hQ.fderiv_right (m := 0) (by norm_num)).continuousAt.comp hq)
  have hdD := happ _ ((hD.fderiv_right (m := 0) (by norm_num)).continuousAt.comp hq)
  have hdC := happ _ ((hC.fderiv_right (m := 0) (by norm_num)).continuousAt.comp hq)
  have hdY := happ _ ((hY.fderiv_right (m := 0) (by norm_num)).continuousAt.comp hq)
  have hdc : ContinuousWithinAt (fun s => originalGaussShear c ![Y (q s),q s 1]) S t := (hD.continuousAt.comp hq).continuousWithinAt
  have hui (i : Fin 2) : ContinuousWithinAt (fun s => u s i) S t := (continuous_apply i).continuousAt.comp_continuousWithinAt hu
  have hqi (i : Fin 2) : ContinuousWithinAt (fun s => q s i) S t := ((continuous_apply i).continuousAt.comp hq).continuousWithinAt
  apply continuousWithinAt_pi.mpr
  intro i
  fin_cases i
  · exact hui 0
  · exact (hdQ.add (hdD.mul (hqi 0))).add (hdc.mul (hui 0))
  · exact hdC
  · exact hdD
  · exact hdY
  · exact hui 1

theorem originalUpperRelativeFrame_derivative_norm_bounds
    (g v : ℝ → Fin 6 → ℝ) (w : ℝ → ℝ) (a z : ℝ) (haz : a ≤ z)
    (hv : ContinuousOn v (Icc a z)) (hg : ∀ t ∈ Icc a z, HasDerivAt g (v t) t)
    (hw : IntervalIntegrable w volume a z) (hw0 : ∀ t ∈ Icc a z, 0 ≤ w t)
    (hbody : ∀ t ∈ Icc a z, ‖originalAffineBodyCoordinates (g t) (v t)‖ ≤ w t) :
    let L := ∫ t in a..z, w t
    let C := L*(1+L)^2
    ‖originalUpperRelativeFrame (g a) (g z)‖ ≤ C ∧
      ‖originalUpperRelativeFrame (g z) (g a)‖ ≤ C*(1+C)^2 := by
  have hgc : ContinuousOn g (Icc a z) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  apply originalUpperRelativeFrame_norm_bounds g (fun t => originalAffineBodyCoordinates (g t) (v t)) w a z haz
    (originalAffineBodyCoordinates_continuousOn g v _ hgc hv) _ hw hw0
  · intro t ht i
    exact (norm_le_pi_norm _ i).trans (hbody t ht)
  · intro t ht
    simpa only [originalUpperBodyVelocity_body] using hg t ht

theorem originalGauss_graph_jets_relative_frame_bounds
    (c Y : (Fin 2 → ℝ) → ℝ) (q u : ℝ → Fin 2 → ℝ) (a z : ℝ) (haz : a ≤ z)
    (hu : ContinuousOn u (Icc a z)) (hq : ∀ t ∈ Icc a z, HasDerivAt q (u t) t)
    (hc : ∀ t ∈ Icc a z, ContDiffAt ℝ 3 c ![Y (q t),q t 1])
    (hY : ∀ t ∈ Icc a z, ContDiffAt ℝ 1 Y (q t))
    (hr : ∀ t ∈ Icc a z, originalGaussR c ![Y (q t),q t 1] ≠ 0)
    (hright : ∀ t ∈ Icc a z, ∀ᶠ v in 𝓝 (q t), originalGaussCy c ![Y v,v 1]=v 0)
    (M : ℝ) (hM : 1 ≤ M)
    (h2 : ∀ t ∈ Icc a z, ‖fderiv ℝ (fderiv ℝ c) ![Y (q t),q t 1]‖ ≤ M^6)
    (h3 : ∀ t ∈ Icc a z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) ![Y (q t),q t 1]‖ ≤ 4*M^10)
    (hi : ∀ t ∈ Icc a z, |(originalGaussR c ![Y (q t),q t 1])⁻¹| ≤ M) :
    let L := 384*M^33*(∫ t in a..z, ‖u t‖)
    let C := L*(1+L)^2
    ‖originalUpperRelativeFrame (originalGaussFrameField c Y (q a))
      (originalGaussFrameField c Y (q z))‖ ≤ C ∧
    ‖originalUpperRelativeFrame (originalGaussFrameField c Y (q z))
      (originalGaussFrameField c Y (q a))‖ ≤ C*(1+C)^2 := by
  have hvel : ContinuousOn (fun t => originalGaussFrameVelocity c Y (q t) (u t)) (Icc a z) := by
    intro t ht
    exact originalGaussFrameVelocity_continuousWithinAt_path c Y q u _ t
      (hq t ht).continuousAt (hu t ht) (hc t ht) (hY t ht) (hr t ht)
  have hpath : ∀ t ∈ Icc a z, HasDerivAt (fun s => originalGaussFrameField c Y (q s))
      (originalGaussFrameVelocity c Y (q t) (u t)) t := fun t ht =>
    originalGaussFrameField_hasDerivAt c Y q t (u t) (hq t ht) (hc t ht)
      ((hY t ht).differentiableAt (by norm_num)) (hr t ht)
  have hw : IntervalIntegrable (fun t => 384*M^33*‖u t‖) volume a z :=
    (((continuousOn_const.mul hu.norm).mono (by rw [uIcc_of_le haz]))).intervalIntegrable
  have hw0 : ∀ t ∈ Icc a z, 0 ≤ 384*M^33*‖u t‖ := by
    intro t ht
    positivity
  have hbody : ∀ t ∈ Icc a z,
      ‖originalAffineBodyCoordinates (originalGaussFrameField c Y (q t))
        (originalGaussFrameVelocity c Y (q t) (u t))‖ ≤ 384*M^33*‖u t‖ := by
    intro t ht
    exact (originalGauss_graph_jets_body_bounds c Y (q t) (hc t ht)
      ((hY t ht).differentiableAt (by norm_num)) (hr t ht) (hright t ht) M hM
      (h2 t ht) (h3 t ht) (hi t ht)).2.2.2.2 (u t)
  have h := originalUpperRelativeFrame_derivative_norm_bounds
    (fun t => originalGaussFrameField c Y (q t))
    (fun t => originalGaussFrameVelocity c Y (q t) (u t))
    (fun t => 384*M^33*‖u t‖) a z haz hvel hpath hw hw0 hbody
  simpa only [intervalIntegral.integral_const_mul] using h

theorem originalAffineHomogeneousMatrix_comp (g h : Fin 6 → ℝ) :
    originalAffineHomogeneousMatrix (originalUpperAffineComp g h) =
      originalAffineHomogeneousMatrix g * originalAffineHomogeneousMatrix h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalAffineHomogeneousMatrix, originalUpperAffineComp, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

theorem originalAffineHomogeneousMatrix_relative (g h : Fin 6 → ℝ) :
    (originalAffineHomogeneousMatrix g)⁻¹ * originalAffineHomogeneousMatrix h =
      originalAffineHomogeneousMatrix (originalUpperRelativeFrame g h) := by
  rw [originalAffineHomogeneousMatrix_inverse, ← originalAffineHomogeneousMatrix_comp]
  rfl

theorem originalAffineHomogeneousMatrix_entry_bound (g : Fin 6 → ℝ) (i j : Fin 4) :
    |originalAffineHomogeneousMatrix g i j| ≤ 1 + ‖g‖ := by
  have h (l : Fin 6) : |g l| ≤ 1 + ‖g‖ := (norm_le_pi_norm g l).trans (by linarith)
  have h0 : 0 ≤ 1 + ‖g‖ := by positivity
  have h1 : 1 ≤ 1 + ‖g‖ := by linarith [norm_nonneg g]
  fin_cases i <;> fin_cases j <;> simp [originalAffineHomogeneousMatrix, h, h0, h1]

theorem originalAffineRelativeMatrix_entry_bounds
    (g h : Fin 6 → ℝ) (C D : ℝ)
    (hforward : ‖originalUpperRelativeFrame g h‖ ≤ C)
    (hreverse : ‖originalUpperRelativeFrame h g‖ ≤ D) :
    (∀ i j : Fin 4,
      |((originalAffineHomogeneousMatrix g)⁻¹ * originalAffineHomogeneousMatrix h) i j| ≤ 1+C) ∧
    (∀ i j : Fin 4,
      |((originalAffineHomogeneousMatrix h)⁻¹ * originalAffineHomogeneousMatrix g) i j| ≤ 1+D) := by
  constructor
  · intro i j
    rw [originalAffineHomogeneousMatrix_relative]
    exact (originalAffineHomogeneousMatrix_entry_bound _ i j).trans (add_le_add_left hforward 1)
  · intro i j
    rw [originalAffineHomogeneousMatrix_relative]
    exact (originalAffineHomogeneousMatrix_entry_bound _ i j).trans (add_le_add_left hreverse 1)

end PaperI
