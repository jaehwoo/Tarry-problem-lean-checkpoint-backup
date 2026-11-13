import PaperILean.AffineAreaGeometry
import PaperILean.AffineAreaFiniteMultiplicity
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open Set MeasureTheory Matrix Filter
open scoped ENNReal BigOperators

namespace PaperI.AffineArea

open PaperI.AffineSurfaceStage (chartNormal chartAreaDensity chartCurvature chartAreaMeasure
  RegularOn area_continuousOn curvature_continuousOn)
open PaperI.AffineSurfaceAlgebra (normal_unit)

local notation "Space" => PaperI.AffineSurfaceDerivatives.Space

private def coordinateBox (center : Plane) (R : ℝ) : Set Plane :=
  univ.pi fun i => Icc (center i - R) (center i + R)

private theorem coordinateBox_measurable (center : Plane) (R : ℝ) :
    MeasurableSet (coordinateBox center R) :=
  MeasurableSet.pi countable_univ fun _ _ => measurableSet_Icc

private theorem coordinateBox_volume (center : Plane) {R : ℝ} (hR : 0 ≤ R) :
    volume (coordinateBox center R) = ENNReal.ofReal (4 * R^2) := by
  rw [coordinateBox, volume_pi, Measure.pi_pi, Fin.prod_univ_two]
  simp only [Real.volume_Icc, show ∀ a : ℝ, a + R - (a - R) = 2 * R from fun _ => by ring]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

private theorem integral_projected_bound (f : Plane → Space) (U E : Set Plane)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hE : MeasurableSet E) (hEU : E ⊆ U)
    (center : Space) (R : ℝ) (hR : 0 ≤ R)
    (hbox : ∀ x ∈ E, ∀ i, |f x i - center i| ≤ R) (N : ℕ)
    (hN : ∀ (i : Fin 3) (y : Plane),
      {x | x ∈ E ∧ (fderiv ℝ (fun p => project i (f p)) x).det ≠ 0 ∧
        project i (f x) = y}.encard ≤ N) :
    (∫⁻ x in E, ENNReal.ofReal (∑ i : Fin 3,
      |(fderiv ℝ (fun p => project i (f p)) x).det|)) ≤
      ENNReal.ofReal (12 * (N : ℝ) * R^2) := by
  let d (i : Fin 3) (x : Plane) := |(fderiv ℝ (fun p => project i (f p)) x).det|
  have hd (i : Fin 3) : ContinuousOn (d i) U := by
    unfold d
    exact (ContinuousLinearMap.continuous_det.comp_continuousOn
      ((project_contDiffOn i hf).continuousOn_fderiv_of_isOpen hU le_rfl)).abs
  have hsum : ∀ x, ENNReal.ofReal (∑ i : Fin 3, d i x) =
      ∑ i : Fin 3, ENNReal.ofReal (d i x) := fun _ =>
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)
  change (∫⁻ x in E, ENNReal.ofReal (∑ i, d i x)) ≤ _
  simp_rw [hsum]
  rw [lintegral_finset_sum' Finset.univ (fun i _ =>
    ((hd i).mono hEU).aemeasurable (μ := volume) hE |>.ennreal_ofReal)]
  have hi (i : Fin 3) : (∫⁻ x in E, ENNReal.ofReal (d i x)) ≤
      ENNReal.ofReal (4 * (N : ℝ) * R^2) := by
    have hto : MapsTo (fun p => project i (f p)) E (coordinateBox (project i center) R) := by
      intro x hx
      apply Set.mem_pi.mpr
      intro j _
      have h := abs_le.mp (hbox x hx (coord i j))
      change center (coord i j) - R ≤ f x (coord i j) ∧ f x (coord i j) ≤ center (coord i j) + R
      constructor
      · linarith
      · linarith
    have h := integral_abs_det_le_mul_volume (fun p => project i (f p)) U E
      (coordinateBox (project i center) R) hU (project_contDiffOn i hf) hE hEU
      (coordinateBox_measurable _ _) hto N (hN i)
    rw [coordinateBox_volume _ hR, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg N)] at h
    convert h using 2 <;> ring
  calc
    _ ≤ ∑ _ : Fin 3, ENNReal.ofReal (4 * (N : ℝ) * R^2) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      congr 1
      simp [Fin.sum_univ_succ]
      ring

theorem chart_area_le_of_projection_fibers (σ : Plane → Space) (U E : Set Plane)
    (hU : IsOpen U) (hσ : ContDiffOn ℝ 2 σ U) (hE : MeasurableSet E) (hEU : E ⊆ U)
    (center : Space) (R : ℝ) (hR : 0 ≤ R)
    (hbox : ∀ x ∈ E, ∀ i, |σ x i - center i| ≤ R) (N : ℕ)
    (hN : ∀ (i : Fin 3) (y : Plane),
      {x | x ∈ E ∧ (fderiv ℝ (fun p => project i (σ p)) x).det ≠ 0 ∧
        project i (σ x) = y}.encard ≤ N) :
    chartAreaMeasure σ (volume.restrict E) univ ≤ ENNReal.ofReal (12 * (N : ℝ) * R^2) := by
  unfold chartAreaMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  apply le_trans _ (integral_projected_bound σ U E hU (hσ.of_le (by norm_num))
    hE hEU center R hR hbox N hN)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hE] with x hx
  exact ENNReal.ofReal_le_ofReal
    (chart_area_le_projected ((hσ.contDiffAt (hU.mem_nhds (hEU hx))).differentiableAt
      (by norm_num)))

theorem chart_total_curvature_le_of_projection_fibers (σ : Plane → Space) (U E : Set Plane)
    (hU : IsOpen U) (hσ : ContDiffOn ℝ 2 σ U) (hr : RegularOn σ U)
    (hE : MeasurableSet E) (hEU : E ⊆ U) (N : ℕ)
    (hN : ∀ (i : Fin 3) (y : Plane),
      {x | x ∈ E ∧ (fderiv ℝ (fun p => project i (chartNormal σ p)) x).det ≠ 0 ∧
        project i (chartNormal σ x) = y}.encard ≤ N) :
    (∫⁻ x, ENNReal.ofReal |chartCurvature σ (chartNormal σ) x|
      ∂chartAreaMeasure σ (volume.restrict E)) ≤ ENNReal.ofReal (12 * (N : ℝ)) := by
  have hnorm := normal_contDiffOn hU hσ hr
  have harea : AEMeasurable (fun x => ENNReal.ofReal (chartAreaDensity σ x))
      (volume.restrict E) :=
    ((area_continuousOn σ U hU hσ).mono hEU).aemeasurable (μ := volume) hE
      |>.ennreal_ofReal
  have hk : AEMeasurable (fun x => ENNReal.ofReal |chartCurvature σ (chartNormal σ) x|)
      (volume.restrict E) := by
    have hc := (curvature_continuousOn σ (chartNormal σ) U hU hσ hr hnorm.continuousOn).abs.mono hEU
    exact (hc.aemeasurable (μ := volume) hE).ennreal_ofReal
  have hbox : ∀ x ∈ E, ∀ i, |chartNormal σ x i - (0 : Space) i| ≤ 1 := by
    intro x hx i
    let n := chartNormal σ x
    have hn : dotProduct n n = 1 := normal_unit _ _ (hr x (hEU hx))
    have hsq : ∑ j : Fin 3, n j ^ 2 = 1 := by
      simpa only [dotProduct, pow_two] using hn
    change |n i - 0| ≤ 1
    rw [sub_zero]
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
    rw [sq_abs]
    rw [one_pow, ← hsq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (n j)) (Finset.mem_univ i)
  unfold chartAreaMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀ harea hk]
  have h := integral_projected_bound (chartNormal σ) U E hU hnorm hE hEU 0 1
    (by norm_num) hbox N hN
  simp only [one_pow, mul_one] at h
  refine le_trans ?_ h
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hE] with x hx
  rw [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (show 0 ≤ chartAreaDensity σ x from Real.sqrt_nonneg _), mul_comm]
  exact ENNReal.ofReal_le_ofReal (chart_curvature_area_le_projected hU hσ hr (hEU hx))

end PaperI.AffineArea
