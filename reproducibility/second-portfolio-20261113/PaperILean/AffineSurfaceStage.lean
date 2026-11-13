import PaperILean.AffineSurfaceAlgebra
import PaperILean.AffineSurfaceDerivatives
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory Matrix Filter
open scoped ENNReal Topology

namespace PaperI.AffineSurfaceStage

open PaperI.AffineSurfaceCross PaperI.AffineSurfaceAlgebra
open PaperI.AffineSurfaceDerivatives

abbrev Plane := Fin 2 → ℝ
abbrev Space := Fin 3 → ℝ

noncomputable def chartNormal (σ : Plane → Space) (x : Plane) : Space :=
  normal (tangent σ 0 x) (tangent σ 1 x)

noncomputable def imageNormal (B : Matrix (Fin 3) (Fin 3) ℝ)
    (σ : Plane → Space) (x : Plane) : Space :=
  transformedNormal B (tangent σ 0 x) (tangent σ 1 x)

noncomputable def chartAreaDensity (σ : Plane → Space) (x : Plane) : ℝ :=
  area (tangent σ 0 x) (tangent σ 1 x)

noncomputable def chartCurvature (σ : Plane → Space) (n : Plane → Space) (x : Plane) : ℝ :=
  curvature (tangent σ 0 x) (tangent σ 1 x) (n x) (secondDerivative σ x)

noncomputable def chartAreaMeasure (σ : Plane → Space) (μ : Measure Plane) : Measure Plane :=
  μ.withDensity (fun x => ENNReal.ofReal (chartAreaDensity σ x))

noncomputable def affineCurvatureArea (σ : Plane → Space) (n : Plane → Space)
    (μ : Measure Plane) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (|chartCurvature σ n x| ^ (1 / 4 : ℝ)) ∂chartAreaMeasure σ μ

def RegularOn (σ : Plane → Space) (U : Set Plane) : Prop :=
  ∀ x ∈ U, 0 < dotProduct (cross (tangent σ 0 x) (tangent σ 1 x))
    (cross (tangent σ 0 x) (tangent σ 1 x))

theorem quarter_density_algebra (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) (hreg : 0 < dotProduct (cross u w) (cross u w)) (H : SecondData) :
    |curvature (B.mulVec u) (B.mulVec w) (transformedNormal B u w)
      (transformedSecondData B H)| ^ (1 / 4 : ℝ) * area (B.mulVec u) (B.mulVec w) =
      |B.det| ^ (1 / 2 : ℝ) * (|curvature u w (normal u w) H| ^ (1 / 4 : ℝ) * area u w) := by
  have hv : 0 < |B.det| := abs_pos.mpr hB
  have ha := alpha_pos B hB u w hreg
  have hd : 0 < |B.det| ^ 2 * alpha B u w ^ 4 := mul_pos (pow_pos hv _) (pow_pos ha _)
  have hp : (|B.det| ^ 2 * alpha B u w ^ 4) ^ (1 / 4 : ℝ) =
      |B.det| ^ (1 / 2 : ℝ) * alpha B u w := by
    rw [Real.mul_rpow (le_of_lt (pow_pos hv 2)) (le_of_lt (pow_pos ha 4))]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hv)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt ha)]
    norm_num
  have hvhalf : |B.det| ^ (1 / 2 : ℝ) * |B.det| ^ (1 / 2 : ℝ) = |B.det| := by
    rw [← Real.rpow_add hv]
    norm_num
  have hvhalf0 : |B.det| ^ (1 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hv _)
  rw [curvature_transformed B hB u w hreg H, abs_div, abs_of_pos hd,
    Real.div_rpow (abs_nonneg _) (le_of_lt hd), hp, area_transformed B hB u w hreg]
  field_simp
  linear_combination -(|curvature u w (normal u w) H| ^ (1 / 4 : ℝ) * alpha B u w * area u w) * hvhalf

theorem pointwise_transform (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (b : Space) (σ : Plane → Space) (x : Plane)
    (hσ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ σ y)
    (h2 : ∀ j : Fin 2, DifferentiableAt ℝ (tangent σ j) x)
    (hreg : 0 < dotProduct (cross (tangent σ 0 x) (tangent σ 1 x))
      (cross (tangent σ 0 x) (tangent σ 1 x))) :
    chartAreaDensity (affine B b σ) x =
      |B.det| * alpha B (tangent σ 0 x) (tangent σ 1 x) * chartAreaDensity σ x ∧
    |chartCurvature (affine B b σ) (imageNormal B σ) x| =
      |chartCurvature σ (chartNormal σ) x| /
        (|B.det| ^ 2 * alpha B (tangent σ 0 x) (tangent σ 1 x) ^ 4) ∧
    |chartCurvature (affine B b σ) (imageNormal B σ) x| ^ (1 / 4 : ℝ) *
      chartAreaDensity (affine B b σ) x = |B.det| ^ (1 / 2 : ℝ) *
        (|chartCurvature σ (chartNormal σ) x| ^ (1 / 4 : ℝ) * chartAreaDensity σ x) := by
  have ht := affine_tangent B b σ x hσ.self_of_nhds
  have hs : secondDerivative (affine B b σ) x = transformedSecondData B (secondDerivative σ x) := by
    funext i j
    exact affine_secondDerivative B b σ x hσ h2 i j
  dsimp [chartAreaDensity, chartCurvature, chartNormal, imageNormal]
  rw [ht 0, ht 1, hs]
  refine ⟨area_transformed B hB _ _ hreg, ?_, quarter_density_algebra B hB _ _ hreg _⟩
  have hp : 0 < |B.det| ^ 2 * alpha B (tangent σ 0 x) (tangent σ 1 x) ^ 4 :=
    mul_pos (pow_pos (abs_pos.mpr hB) _) (pow_pos (alpha_pos B hB _ _ hreg) _)
  rw [curvature_transformed B hB _ _ hreg, abs_div, abs_of_pos hp]

theorem continuousOn_dot {U : Set Plane} {f g : Plane → Space}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) :
    ContinuousOn (fun x => dotProduct (f x) (g x)) U := by
  have h (i : Fin 3) := (continuousOn_pi.mp hf i).mul (continuousOn_pi.mp hg i)
  simpa [dotProduct, Fin.sum_univ_succ] using (h 0).add ((h 1).add (h 2))

theorem continuousOn_cross {U : Set Plane} {f g : Plane → Space}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) :
    ContinuousOn (fun x => cross (f x) (g x)) U := by
  apply continuousOn_pi.mpr
  intro i
  have h (j k : Fin 3) := (continuousOn_pi.mp hf j).mul (continuousOn_pi.mp hg k)
  fin_cases i
  · simpa [cross] using (h 1 2).sub (h 2 1)
  · simpa [cross] using (h 2 0).sub (h 0 2)
  · simpa [cross] using (h 0 1).sub (h 1 0)

theorem continuousOn_gram_det {U : Set Plane} {f g : Plane → Space}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) :
    ContinuousOn (fun x => (gram (f x) (g x)).det) U := by
  simpa [gram, Matrix.det_fin_two] using
    ((continuousOn_dot hf hf).mul (continuousOn_dot hg hg)).sub
      ((continuousOn_dot hf hg).mul (continuousOn_dot hg hf))

theorem tangent_continuousOn (σ : Plane → Space) (U : Set Plane) (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (j : Fin 2) : ContinuousOn (tangent σ j) U := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ σ) U := hσ.fderiv_of_isOpen hU (by norm_num)
  exact hd.continuousOn.clm_apply continuousOn_const

theorem area_continuousOn (σ : Plane → Space) (U : Set Plane) (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) : ContinuousOn (chartAreaDensity σ) U :=
  (continuousOn_gram_det (tangent_continuousOn σ U hU hσ 0)
    (tangent_continuousOn σ U hU hσ 1)).sqrt

theorem normal_continuousOn (σ : Plane → Space) (U : Set Plane) (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (hr : RegularOn σ U) : ContinuousOn (chartNormal σ) U := by
  have ha := area_continuousOn σ U hU hσ
  have hcross := continuousOn_cross (tangent_continuousOn σ U hU hσ 0)
    (tangent_continuousOn σ U hU hσ 1)
  exact (ha.inv₀ (fun x hx => ne_of_gt (area_pos _ _ (hr x hx)))).smul hcross

theorem imageNormal_continuousOn (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (σ : Plane → Space) (U : Set Plane) (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (hr : RegularOn σ U) : ContinuousOn (imageNormal B σ) U := by
  have hn := normal_continuousOn σ U hU hσ hr
  have ht : ContinuousOn (fun x => transport B (chartNormal σ x)) U := by
    simpa only [transport, matrixCLM_apply] using
      (matrixCLM (B⁻¹).transpose).continuous.comp_continuousOn hn
  have ha : ContinuousOn (fun x => alpha B (tangent σ 0 x) (tangent σ 1 x)) U :=
    (continuousOn_dot ht ht).sqrt
  exact (ha.inv₀ (fun x hx => ne_of_gt (alpha_pos B hB _ _ (hr x hx)))).smul ht

theorem curvature_continuousOn (σ n : Plane → Space) (U : Set Plane) (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (hr : RegularOn σ U) (hn : ContinuousOn n U) :
    ContinuousOn (chartCurvature σ n) U := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ σ) U := hσ.fderiv_of_isOpen hU (by norm_num)
  have hj (j : Fin 2) : ContDiffOn ℝ 1 (tangent σ j) U := hd.clm_apply contDiffOn_const
  have hh (i j : Fin 2) : ContinuousOn (fun x => secondDerivative σ x i j) U := by
    have h : ContDiffOn ℝ 0 (fderiv ℝ (tangent σ j)) U :=
      (hj j).fderiv_of_isOpen hU (by norm_num)
    exact h.continuousOn.clm_apply continuousOn_const
  have hII (i j : Fin 2) := continuousOn_dot hn (hh i j)
  have hdet : ContinuousOn (fun x => (secondForm (n x) (secondDerivative σ x)).det) U := by
    simpa only [Matrix.det_fin_two, secondForm] using
      ((hII 0 0).mul (hII 1 1)).sub ((hII 0 1).mul (hII 1 0))
  exact hdet.div (continuousOn_gram_det (tangent_continuousOn σ U hU hσ 0)
    (tangent_continuousOn σ U hU hσ 1)) (fun x hx => by
      rw [← cross_dot_self]
      exact ne_of_gt (hr x hx))

theorem affine_regularOn (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (b : Space) (σ : Plane → Space) (U : Set Plane) (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (hr : RegularOn σ U) : RegularOn (affine B b σ) U := by
  intro x hx
  have hd := (regularity_on σ U hU hσ x hx).1.self_of_nhds
  rw [affine_tangent B b σ x hd 0, affine_tangent B b σ x hd 1, cross_dot_self,
    gram_transformed B hB _ _ (hr x hx), ← cross_dot_self]
  exact mul_pos (sq_pos_of_pos (mul_pos (abs_pos.mpr hB) (alpha_pos B hB _ _ (hr x hx)))) (hr x hx)

/-- The normal fields used in the curvature integrals are actual unit normals. -/
theorem chart_normals_valid (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (b : Space) (σ : Plane → Space) (x : Plane) (hσ : DifferentiableAt ℝ σ x)
    (hreg : 0 < dotProduct (cross (tangent σ 0 x) (tangent σ 1 x))
      (cross (tangent σ 0 x) (tangent σ 1 x))) :
    dotProduct (chartNormal σ x) (chartNormal σ x) = 1 ∧
    dotProduct (chartNormal σ x) (tangent σ 0 x) = 0 ∧
    dotProduct (chartNormal σ x) (tangent σ 1 x) = 0 ∧
    dotProduct (imageNormal B σ x) (imageNormal B σ x) = 1 ∧
    dotProduct (imageNormal B σ x) (tangent (affine B b σ) 0 x) = 0 ∧
    dotProduct (imageNormal B σ x) (tangent (affine B b σ) 1 x) = 0 := by
  dsimp [chartNormal, imageNormal]
  rw [affine_tangent B b σ x hσ 0, affine_tangent B b σ x hσ 1]
  exact ⟨normal_unit _ _ hreg, normal_left _ _, normal_right _ _,
    transformedNormal_unit B hB _ _ hreg, transformedNormal_left B hB _ _,
    transformedNormal_right B hB _ _⟩

/-- Affine covariance of the curvature integral in a common regular C²
parameter chart. For noninjective parametrizations this integral retains
parameter multiplicity; no set-image or Hausdorff-measure formula is asserted. -/
theorem affine_curvature_area_stage (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (b : Space) (σ : Plane → Space) (U E : Set Plane) (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (hr : RegularOn σ U)
    (hE : MeasurableSet E) (hEU : E ⊆ U) :
    (∀ x ∈ U,
      chartAreaDensity (affine B b σ) x =
        |B.det| * alpha B (tangent σ 0 x) (tangent σ 1 x) * chartAreaDensity σ x ∧
      |chartCurvature (affine B b σ) (imageNormal B σ) x| =
        |chartCurvature σ (chartNormal σ) x| /
          (|B.det| ^ 2 * alpha B (tangent σ 0 x) (tangent σ 1 x) ^ 4)) ∧
    affineCurvatureArea (affine B b σ) (imageNormal B σ) (volume.restrict E) =
      ENNReal.ofReal (|B.det| ^ (1 / 2 : ℝ)) *
        affineCurvatureArea σ (chartNormal σ) (volume.restrict E) := by
  have hs := affine_contDiffOn B b σ U hσ
  have hrr := affine_regularOn B hB b σ U hU hσ hr
  have ha := (((area_continuousOn σ U hU hσ).mono hEU).aemeasurable (μ := volume) hE).ennreal_ofReal
  have haB := (((area_continuousOn (affine B b σ) U hU hs).mono hEU).aemeasurable (μ := volume) hE).ennreal_ofReal
  have hk := (curvature_continuousOn σ (chartNormal σ) U hU hσ hr
    (normal_continuousOn σ U hU hσ hr)).abs
  have hkB := (curvature_continuousOn (affine B b σ) (imageNormal B σ) U hU hs hrr
    (imageNormal_continuousOn B hB σ U hU hσ hr)).abs
  have hq : AEMeasurable (fun x => ENNReal.ofReal (|chartCurvature σ (chartNormal σ) x| ^ (1 / 4 : ℝ))) (volume.restrict E) := (((hk.rpow_const (fun _ _ => Or.inr (by norm_num))).mono hEU).aemeasurable (μ := volume) hE).ennreal_ofReal
  have hqB : AEMeasurable (fun x => ENNReal.ofReal (|chartCurvature (affine B b σ) (imageNormal B σ) x| ^ (1 / 4 : ℝ))) (volume.restrict E) := (((hkB.rpow_const (fun _ _ => Or.inr (by norm_num))).mono hEU).aemeasurable (μ := volume) hE).ennreal_ofReal
  constructor
  · intro x hx
    have ht := pointwise_transform B hB b σ x (regularity_on σ U hU hσ x hx).1
      (regularity_on σ U hU hσ x hx).2 (hr x hx)
    exact ⟨ht.1, ht.2.1⟩
  · unfold affineCurvatureArea chartAreaMeasure
    rw [lintegral_withDensity_eq_lintegral_mul₀ haB hqB,
      lintegral_withDensity_eq_lintegral_mul₀ ha hq,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hE] with x hx
    have hd := (pointwise_transform B hB b σ x (regularity_on σ U hU hσ x (hEU hx)).1
      (regularity_on σ U hU hσ x (hEU hx)).2 (hr x (hEU hx))).2.2
    dsimp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (show 0 ≤ chartAreaDensity (affine B b σ) x from Real.sqrt_nonneg _),
      ← ENNReal.ofReal_mul (show 0 ≤ chartAreaDensity σ x from Real.sqrt_nonneg _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
    congr 1
    simpa only [mul_comm (chartAreaDensity (affine B b σ) x), mul_comm (chartAreaDensity σ x)] using hd

end PaperI.AffineSurfaceStage
