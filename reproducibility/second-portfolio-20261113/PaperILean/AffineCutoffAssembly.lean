import PaperILean.GraphChartBridge
import PaperILean.AffineCurvatureHolder
import PaperILean.AffineCutoffScalar

open MeasureTheory Matrix Filter
open scoped ENNReal Topology

namespace PaperI.AffineCutoffAssembly

open PaperI.GraphCurvatureDensity PaperI.AffineSurfaceStage
open PaperI.AffineSurfaceDerivatives PaperI.AffineGraphStage
open PaperI.GraphChartBridge

abbrev Plane := Fin 2 → ℝ
abbrev Space := Fin 3 → ℝ

/-- I3339[147,185): the Hessian lower bound controls the genuine graph
affine-curvature area, without assuming finite parameter volume. -/
theorem graph_hessian_lower_bound (κ : ℝ) (hκ : 0 < κ)
    (c : Plane → ℝ) (U E : Set Plane) (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 c U) (hE : MeasurableSet E) (hEU : E ⊆ U)
    (hH : ∀ x ∈ E, κ ≤ |(hessian c x).det|) :
    ENNReal.ofReal (κ ^ (1 / 4 : ℝ)) * volume E ≤
      affineCurvatureArea (graph c) (chartNormal (graph c)) (volume.restrict E) := by
  rw [graph_affine_area_eq_hessian c U E hU hc hE hEU]
  calc
    ENNReal.ofReal (κ ^ (1 / 4 : ℝ)) * volume E =
        ∫⁻ _x, ENNReal.ofReal (κ ^ (1 / 4 : ℝ)) ∂volume.restrict E := by
      simp only [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ x, ENNReal.ofReal (|(hessian c x).det| ^ (1 / 4 : ℝ)) ∂volume.restrict E := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hE] with x hx
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (le_of_lt hκ) (hH x hx) (by norm_num))

/-- The curvature used in the physical integral is measurable for the actual
physical chart area measure; this is derived from C² regularity. -/
theorem physical_curvature_aemeasurable
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) (b : Space)
    (c : Plane → ℝ) (U E : Set Plane) (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 c U) (hE : MeasurableSet E) (hEU : E ⊆ U) :
    AEMeasurable
      (chartCurvature (affine B b (graph c)) (chartNormal (affine B b (graph c))))
      (chartAreaMeasure (affine B b (graph c)) (volume.restrict E)) := by
  have hgraph := graph_contDiffOn c U hc
  have hr : RegularOn (graph c) U := by
    intro x hx
    exact graph_regular c x ((hc.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
  have hphys := affine_contDiffOn B b (graph c) U hgraph
  have hreg := affine_regularOn B hB b (graph c) U hU hgraph hr
  have hcontinuous := curvature_continuousOn (affine B b (graph c))
    (chartNormal (affine B b (graph c))) U hU hphys hreg
    (normal_continuousOn (affine B b (graph c)) U hU hphys hreg)
  exact ((hcontinuous.mono hEU).aemeasurable (μ := volume) hE).mono'
    (withDensity_absolutelyContinuous _ _)

/-- I3339[101,186): the final cutoff inference for the actual affine graph.
The two geometric estimates from I3325 are explicit remaining premises.
Their constants are fixed before the radius and all graph and affine data. -/
theorem affine_surface_cutoff_from_geometric_bounds
    (Ccurv Carea : ℝ) (hCcurv : 0 ≤ Ccurv) (hCarea : 0 ≤ Carea)
    (R : ℝ) (hR : 0 ≤ R) (κ : ℝ) (hκ : 0 < κ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) (b : Space)
    (c : Plane → ℝ) (U E : Set Plane) (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 c U) (hE : MeasurableSet E) (hEU : E ⊆ U)
    (hH : ∀ x ∈ E, κ ≤ |(hessian c x).det|)
    (hcurv : (∫⁻ x, ENNReal.ofReal
      |chartCurvature (affine B b (graph c)) (chartNormal (affine B b (graph c))) x|
      ∂chartAreaMeasure (affine B b (graph c)) (volume.restrict E)) ≤ ENNReal.ofReal Ccurv)
    (harea : chartAreaMeasure (affine B b (graph c)) (volume.restrict E) Set.univ ≤
      ENNReal.ofReal (Carea * R ^ 2)) :
    volume E ≤ ENNReal.ofReal
      (Ccurv ^ (1 / 4 : ℝ) * Carea ^ (3 / 4 : ℝ) * R ^ (3 / 2 : ℝ) *
        κ ^ (-1 / 4 : ℝ) * |B.det| ^ (-1 / 2 : ℝ)) ∧
    volume E ≠ ∞ ∧
    (volume E).toReal ≤
      Ccurv ^ (1 / 4 : ℝ) * Carea ^ (3 / 4 : ℝ) * R ^ (3 / 2 : ℝ) *
        κ ^ (-1 / 4 : ℝ) * |B.det| ^ (-1 / 2 : ℝ) := by
  let μB := chartAreaMeasure (affine B b (graph c)) (volume.restrict E)
  let KB := chartCurvature (affine B b (graph c)) (chartNormal (affine B b (graph c)))
  have hKB : AEMeasurable KB μB :=
    physical_curvature_aemeasurable B hB b c U E hU hc hE hEU
  have hh := PaperI.AffineCurvatureHolder.affine_curvature_holder_stage
    Ccurv Carea hCcurv hCarea R hR Plane μB KB hKB hcurv harea
  have hphysical : affineCurvatureArea (affine B b (graph c))
      (chartNormal (affine B b (graph c))) (volume.restrict E) ≤
      ENNReal.ofReal (Ccurv ^ (1 / 4 : ℝ) * Carea ^ (3 / 4 : ℝ) * R ^ (3 / 2 : ℝ)) := by
    change (∫⁻ x, ENNReal.ofReal (|KB x| ^ (1 / 4 : ℝ)) ∂μB) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hh.2.1
      (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg (KB x)) _)]
    exact ENNReal.ofReal_le_ofReal hh.2.2.2
  exact PaperI.AffineCutoffScalar.cutoff_scalar (volume E)
    (affineCurvatureArea (graph c) (chartNormal (graph c)) (volume.restrict E))
    (affineCurvatureArea (affine B b (graph c))
      (chartNormal (affine B b (graph c))) (volume.restrict E))
    κ |B.det| (Ccurv ^ (1 / 4 : ℝ) * Carea ^ (3 / 4 : ℝ) * R ^ (3 / 2 : ℝ))
    hκ (abs_pos.mpr hB) (by positivity)
    (graph_hessian_lower_bound κ hκ c U E hU hc hE hEU hH)
    (graph_affine_curvature_area_stage B hB b c U E hU hc hE hEU).2.2 hphysical

end PaperI.AffineCutoffAssembly
