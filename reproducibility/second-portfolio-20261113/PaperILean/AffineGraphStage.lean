import PaperILean.GraphCurvatureDensity
import PaperILean.AffineSurfaceCanonical
import PaperILean.AffineSurfaceAlgebra
import PaperILean.AffineSurfaceDerivatives

open Matrix MeasureTheory
open scoped ENNReal

namespace PaperI.AffineGraphStage


theorem graph_injective (c : PaperI.GraphCurvatureDensity.Plane → ℝ) : Function.Injective (PaperI.GraphCurvatureDensity.graph c) := by
  intro x y h
  ext i
  fin_cases i
  · simpa [PaperI.GraphCurvatureDensity.graph] using congrFun h 1
  · simpa [PaperI.GraphCurvatureDensity.graph] using congrFun h 2

theorem graph_contDiffOn (c : PaperI.GraphCurvatureDensity.Plane → ℝ) (U : Set PaperI.GraphCurvatureDensity.Plane)
    (hc : ContDiffOn ℝ 2 c U) : ContDiffOn ℝ 2 (PaperI.GraphCurvatureDensity.graph c) U := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact hc
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).contDiff.contDiffOn
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).contDiff.contDiffOn

theorem graph_tangent (c : PaperI.GraphCurvatureDensity.Plane → ℝ) (x : PaperI.GraphCurvatureDensity.Plane)
    (hc : DifferentiableAt ℝ c x) (j : Fin 2) :
    PaperI.AffineSurfaceDerivatives.tangent (PaperI.GraphCurvatureDensity.graph c) j x = PaperI.GraphCurvatureDensity.tangent (PaperI.GraphCurvatureDensity.gradient c x) j :=
  PaperI.GraphCurvatureDensity.graph_tangent c x hc j

theorem graph_cross (c : PaperI.GraphCurvatureDensity.Plane → ℝ) (x : PaperI.GraphCurvatureDensity.Plane)
    (hc : DifferentiableAt ℝ c x) :
    PaperI.AffineSurfaceCross.cross (PaperI.AffineSurfaceDerivatives.tangent (PaperI.GraphCurvatureDensity.graph c) 0 x) (PaperI.AffineSurfaceDerivatives.tangent (PaperI.GraphCurvatureDensity.graph c) 1 x) =
      ![1, -PaperI.GraphCurvatureDensity.gradient c x 0, -PaperI.GraphCurvatureDensity.gradient c x 1] := by
  rw [graph_tangent c x hc, graph_tangent c x hc]
  ext i
  fin_cases i <;> simp [PaperI.AffineSurfaceCross.cross, PaperI.GraphCurvatureDensity.tangent, PaperI.GraphCurvatureDensity.basis]

theorem graph_regular (c : PaperI.GraphCurvatureDensity.Plane → ℝ) (x : PaperI.GraphCurvatureDensity.Plane)
    (hc : DifferentiableAt ℝ c x) :
    0 < dotProduct (PaperI.AffineSurfaceCross.cross (PaperI.AffineSurfaceDerivatives.tangent (PaperI.GraphCurvatureDensity.graph c) 0 x) (PaperI.AffineSurfaceDerivatives.tangent (PaperI.GraphCurvatureDensity.graph c) 1 x))
      (PaperI.AffineSurfaceCross.cross (PaperI.AffineSurfaceDerivatives.tangent (PaperI.GraphCurvatureDensity.graph c) 0 x) (PaperI.AffineSurfaceDerivatives.tangent (PaperI.GraphCurvatureDensity.graph c) 1 x)) := by
  rw [graph_cross c x hc]
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (PaperI.GraphCurvatureDensity.gradient c x 0), sq_nonneg (PaperI.GraphCurvatureDensity.gradient c x 1)]

theorem affine_graph_injective (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.det ≠ 0) (b : PaperI.GraphCurvatureDensity.Space) (c : PaperI.GraphCurvatureDensity.Plane → ℝ) :
    Function.Injective (PaperI.AffineSurfaceDerivatives.affine B b (PaperI.GraphCurvatureDensity.graph c)) := by
  intro x y h
  apply graph_injective c
  have he : B.mulVec (PaperI.GraphCurvatureDensity.graph c x) = B.mulVec (PaperI.GraphCurvatureDensity.graph c y) := add_left_cancel h
  have hi := congrArg (B⁻¹).mulVec he
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB),
    Matrix.one_mulVec] using hi

open PaperI.GraphCurvatureDensity PaperI.AffineSurfaceDerivatives
open PaperI.AffineSurfaceAlgebra PaperI.AffineSurfaceStage PaperI.AffineSurfaceCanonical

/-- The manuscript's graph branch is an injective regular chart. This specializes
all affine transformation conclusions without an extra regularity assumption. -/
theorem graph_affine_curvature_area_stage (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.det ≠ 0) (b : Fin 3 → ℝ) (c : (Fin 2 → ℝ) → ℝ)
    (U E : Set (Fin 2 → ℝ)) (hU : IsOpen U) (hc : ContDiffOn ℝ 2 c U)
    (hE : MeasurableSet E) (hEU : E ⊆ U) :
    Function.Injective (affine B b (graph c)) ∧
    (∀ x ∈ U,
      chartAreaDensity (affine B b (graph c)) x =
        |B.det| * alpha B (PaperI.AffineSurfaceDerivatives.tangent (graph c) 0 x)
          (PaperI.AffineSurfaceDerivatives.tangent (graph c) 1 x) * chartAreaDensity (graph c) x ∧
      |chartCurvature (affine B b (graph c)) (chartNormal (affine B b (graph c))) x| =
        |chartCurvature (graph c) (chartNormal (graph c)) x| /
          (|B.det| ^ 2 * alpha B (PaperI.AffineSurfaceDerivatives.tangent (graph c) 0 x)
            (PaperI.AffineSurfaceDerivatives.tangent (graph c) 1 x) ^ 4)) ∧
    affineCurvatureArea (affine B b (graph c)) (chartNormal (affine B b (graph c)))
      (volume.restrict E) = ENNReal.ofReal (|B.det| ^ (1 / 2 : ℝ)) *
        affineCurvatureArea (graph c) (chartNormal (graph c)) (volume.restrict E) := by
  refine ⟨affine_graph_injective B hB b c, ?_⟩
  apply affine_curvature_area_canonical_stage B hB b (graph c) U E hU
    (graph_contDiffOn c U hc) ?_ hE hEU
  intro x hx
  exact graph_regular c x ((hc.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))

end PaperI.AffineGraphStage
