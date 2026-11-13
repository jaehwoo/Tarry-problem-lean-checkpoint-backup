import PaperILean.AffineGraphStage

open Matrix MeasureTheory
open scoped ENNReal Topology

namespace PaperI.GraphChartBridge

open PaperI.AffineSurfaceCross PaperI.AffineSurfaceAlgebra
open PaperI.AffineSurfaceDerivatives PaperI.AffineSurfaceStage

abbrev Plane := Fin 2 → ℝ

theorem graph_gram_eq (c : Plane → ℝ) (x : Plane) :
    gram (tangent (GraphCurvatureDensity.graph c) 0 x)
      (tangent (GraphCurvatureDensity.graph c) 1 x) =
        GraphCurvatureDensity.actualFirstForm c x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, tangent, basis, GraphCurvatureDensity.actualFirstForm,
      GraphCurvatureDensity.basis]

theorem graph_areaDensity_eq (c : Plane → ℝ) (x : Plane) :
    chartAreaDensity (GraphCurvatureDensity.graph c) x =
      GraphCurvatureDensity.graphAreaDensity c x := by
  simp only [chartAreaDensity, area, graph_gram_eq, GraphCurvatureDensity.graphAreaDensity]

theorem graph_areaMeasure_eq (c : Plane → ℝ) (μ : Measure Plane) :
    chartAreaMeasure (GraphCurvatureDensity.graph c) μ =
      GraphCurvatureDensity.graphAreaMeasure c μ := by
  simp only [chartAreaMeasure, GraphCurvatureDensity.graphAreaMeasure, graph_areaDensity_eq]

theorem graph_normal_eq (c : Plane → ℝ) (x : Plane)
    (hc : DifferentiableAt ℝ c x) :
    chartNormal (GraphCurvatureDensity.graph c) x =
      GraphCurvatureDensity.normal (GraphCurvatureDensity.gradient c x) := by
  have hg : gram (tangent (GraphCurvatureDensity.graph c) 0 x)
      (tangent (GraphCurvatureDensity.graph c) 1 x) =
      GraphCurvatureDensity.firstForm (GraphCurvatureDensity.gradient c x) := by
    rw [AffineGraphStage.graph_tangent c x hc, AffineGraphStage.graph_tangent c x hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gram, GraphCurvatureDensity.firstForm]
  have ha : area (tangent (GraphCurvatureDensity.graph c) 0 x)
      (tangent (GraphCurvatureDensity.graph c) 1 x) =
      Real.sqrt (GraphCurvatureDensity.weight (GraphCurvatureDensity.gradient c x)) := by
    rw [area, hg, GraphCurvatureDensity.firstForm_det]
  unfold chartNormal normal
  rw [ha, AffineGraphStage.graph_cross c x hc]
  ext i
  simp [GraphCurvatureDensity.normal, div_eq_mul_inv, mul_comm]

theorem graph_curvature_eq (c : Plane → ℝ) (x : Plane)
    (hc : DifferentiableAt ℝ c x) :
    chartCurvature (GraphCurvatureDensity.graph c)
      (chartNormal (GraphCurvatureDensity.graph c)) x =
      GraphCurvatureDensity.gaussianCurvature c x := by
  unfold chartCurvature curvature
  rw [graph_normal_eq c x hc, graph_gram_eq]
  rfl

/-- Equality of the two accepted chart APIs; no surface identity is assumed. -/
theorem graph_affine_area_eq_hessian (c : Plane → ℝ) (U E : Set Plane)
    (hU : IsOpen U) (hc : ContDiffOn ℝ 2 c U) (hE : MeasurableSet E) (hEU : E ⊆ U) :
    affineCurvatureArea (GraphCurvatureDensity.graph c)
      (chartNormal (GraphCurvatureDensity.graph c)) (volume.restrict E) =
      ∫⁻ x, ENNReal.ofReal (|(GraphCurvatureDensity.hessian c x).det| ^ (1 / 4 : ℝ))
        ∂volume.restrict E := by
  rw [← (GraphCurvatureDensity.graph_curvature_area_stage c U E hU hc hE hEU).2]
  unfold affineCurvatureArea
  rw [graph_areaMeasure_eq]
  apply lintegral_congr_ae
  have hu : ∀ᵐ x ∂volume.restrict E, DifferentiableAt ℝ c x := by
    filter_upwards [ae_restrict_mem hE] with x hx
    exact (hc.contDiffAt (hU.mem_nhds (hEU hx))).differentiableAt (by norm_num)
  have hs := (withDensity_absolutelyContinuous (volume.restrict E)
    (fun x => ENNReal.ofReal (GraphCurvatureDensity.graphAreaDensity c x))).ae_le hu
  filter_upwards [hs] with x hx
  rw [graph_curvature_eq c x hx]

end PaperI.GraphChartBridge
