import PaperILean.AffineSurfaceStage

open MeasureTheory Matrix Filter
open scoped ENNReal Topology

namespace PaperI.AffineSurfaceCanonical

open PaperI.AffineSurfaceCross PaperI.AffineSurfaceAlgebra
open PaperI.AffineSurfaceDerivatives PaperI.AffineSurfaceStage

abbrev Plane := Fin 2 → ℝ
abbrev Space := Fin 3 → ℝ

/-- The canonical cross-product normal and the transported unit normal give
the same Gaussian curvature, including orientation-reversing affine maps. -/
theorem canonical_curvature_eq (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (b : Space) (σ : Plane → Space) (x : Plane)
    (hσ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ σ y)
    (h2 : ∀ j : Fin 2, DifferentiableAt ℝ (tangent σ j) x)
    (hreg : 0 < dotProduct (cross (tangent σ 0 x) (tangent σ 1 x))
      (cross (tangent σ 0 x) (tangent σ 1 x))) :
    chartCurvature (affine B b σ) (chartNormal (affine B b σ)) x =
      chartCurvature (affine B b σ) (imageNormal B σ) x := by
  have ht := affine_tangent B b σ x hσ.self_of_nhds
  have hs : secondDerivative (affine B b σ) x = transformedSecondData B (secondDerivative σ x) := by
    funext i j
    exact affine_secondDerivative B b σ x hσ h2 i j
  dsimp [chartCurvature, chartNormal, imageNormal]
  rw [ht 0, ht 1, hs, curvature_canonical_transformed B hB _ _ hreg,
    curvature_transformed B hB _ _ hreg]

theorem canonical_integral_eq (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (b : Space) (σ : Plane → Space) (U E : Set Plane) (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (hr : RegularOn σ U)
    (hE : MeasurableSet E) (hEU : E ⊆ U) :
    affineCurvatureArea (affine B b σ) (chartNormal (affine B b σ)) (volume.restrict E) =
      affineCurvatureArea (affine B b σ) (imageNormal B σ) (volume.restrict E) := by
  have he : ∀ᵐ x ∂volume.restrict E,
      chartCurvature (affine B b σ) (chartNormal (affine B b σ)) x =
        chartCurvature (affine B b σ) (imageNormal B σ) x := by
    filter_upwards [ae_restrict_mem hE] with x hx
    exact canonical_curvature_eq B hB b σ x (regularity_on σ U hU hσ x (hEU hx)).1
      (regularity_on σ U hU hσ x (hEU hx)).2 (hr x (hEU hx))
  unfold affineCurvatureArea chartAreaMeasure
  apply lintegral_congr_ae
  filter_upwards [(withDensity_absolutelyContinuous (volume.restrict E)
    (fun x => ENNReal.ofReal (chartAreaDensity (affine B b σ) x))).ae_le he] with x hx
  rw [hx]

/-- I3335-I3338 and I3339[0,44), in a common regular C² parameter chart.
Both curvature integrals use their own canonical cross-product normals.
Noninjective parametrizations retain parameter multiplicity. -/
theorem affine_curvature_area_canonical_stage
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (b : Space) (σ : Plane → Space) (U E : Set Plane) (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (hr : RegularOn σ U)
    (hE : MeasurableSet E) (hEU : E ⊆ U) :
    (∀ x ∈ U,
      chartAreaDensity (affine B b σ) x =
        |B.det| * alpha B (tangent σ 0 x) (tangent σ 1 x) * chartAreaDensity σ x ∧
      |chartCurvature (affine B b σ) (chartNormal (affine B b σ)) x| =
        |chartCurvature σ (chartNormal σ) x| /
          (|B.det| ^ 2 * alpha B (tangent σ 0 x) (tangent σ 1 x) ^ 4)) ∧
    affineCurvatureArea (affine B b σ) (chartNormal (affine B b σ)) (volume.restrict E) =
      ENNReal.ofReal (|B.det| ^ (1 / 2 : ℝ)) *
        affineCurvatureArea σ (chartNormal σ) (volume.restrict E) := by
  have ht := affine_curvature_area_stage B hB b σ U E hU hσ hr hE hEU
  constructor
  · intro x hx
    rw [canonical_curvature_eq B hB b σ x (regularity_on σ U hU hσ x hx).1
      (regularity_on σ U hU hσ x hx).2 (hr x hx)]
    exact ht.1 x hx
  · rw [canonical_integral_eq B hB b σ U E hU hσ hr hE hEU]
    exact ht.2

end PaperI.AffineSurfaceCanonical
