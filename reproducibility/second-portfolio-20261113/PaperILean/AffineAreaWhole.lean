import PaperILean.AffineAreaFibers
import PaperILean.AffineAreaIntegral
import PaperILean.AffineDefiningPolynomial
import PaperILean.AffineCutoffAssembly

open Set Matrix MeasureTheory MvPolynomial
open scoped ENNReal

namespace PaperI.AffineArea

open PaperI.AffineSurfaceDerivatives (affine matrixCLM matrixCLM_apply affine_contDiffOn)
open PaperI.AffineSurfaceStage (RegularOn affine_regularOn)
open PaperI.GraphCurvatureDensity (graph hessian)
open PaperI.AffineGraphStage (affine_graph_injective graph_contDiffOn graph_regular)
open PaperI.AffineDefiningPolynomial (transformedEquation transformed_equation_eval_image
  transformed_equation_degree)

local notation "Space" => PaperI.AffineSurfaceDerivatives.Space

theorem physical_equation_gradient_ne_zero
    (b : Space) (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) (G : Equation)
    (x : Space) (hG : gradient G x ≠ 0) :
    gradient (transformedEquation b B G) (PaperI.affinePoint b B x) ≠ 0 := by
  let A : Space → Space := PaperI.affinePoint b B
  have hA : HasFDerivAt A (matrixCLM B) x := by
    simpa only [A, PaperI.AffineDefiningPolynomial.affinePoint_eq, matrixCLM_apply] using
      ((matrixCLM B).hasFDerivAt.const_add b)
  have he : (fun y => MvPolynomial.eval (A y) (transformedEquation b B G)) =
      fun y => MvPolynomial.eval y G := by
    funext y
    exact transformed_equation_eval_image b B hB G y
  intro hz
  apply hG
  have hd := ((PaperI.RationalCount.polynomial_hasFDerivAt (transformedEquation b B G)
    (A x)).comp x hA).fderiv
  change fderiv ℝ (fun y => MvPolynomial.eval (A y) (transformedEquation b B G)) x = _ at hd
  rw [he, (PaperI.RationalCount.polynomial_hasFDerivAt G x).fderiv] at hd
  ext j
  have h := congrArg (fun L : Space →L[ℝ] ℝ => L (Pi.single j 1)) hd
  change PaperI.RationalCount.polynomialDifferential G x (Pi.single j 1) =
    PaperI.RationalCount.polynomialDifferential (transformedEquation b B G) (A x)
      (matrixCLM B (Pi.single j 1)) at h
  have hh := (differential_eq_gradient_dot G x (Pi.single j 1)).symm.trans
    (h.trans (differential_eq_gradient_dot (transformedEquation b B G) (A x)
      (matrixCLM B (Pi.single j 1))))
  change gradient (transformedEquation b B G) (A x) = 0 at hz
  simpa [hz, dotProduct, Pi.single_apply] using hh

private theorem euclidean_ball_coord {R : ℝ} {a u : Space}
    (hu : (EuclideanSpace.equiv (Fin 3) ℝ).symm u ∈
      Metric.closedBall ((EuclideanSpace.equiv (Fin 3) ℝ).symm a) R) (i : Fin 3) :
    |u i - a i| ≤ R := by
  let u' := (EuclideanSpace.equiv (Fin 3) ℝ).symm u
  let a' := (EuclideanSpace.equiv (Fin 3) ℝ).symm a
  have h : ‖u' - a'‖ ≤ R := by
    simpa only [u', a', dist_eq_norm] using (Metric.mem_closedBall.mp hu)
  have hi := PiLp.norm_apply_le (u' - a') i
  change ‖u i - a i‖ ≤ ‖u' - a'‖ at hi
  exact (Real.norm_eq_abs _ ▸ hi).trans h

/-- I3312–I3317, proof I3318–I3340. Degree-uniform cutoff for the actual
regular graph branch and actual physical affine image. The regular equation
is the selected defining equation, with nonzero differential along the graph.
The sole explicit published input is the accepted polynomial Bézout bound. -/
theorem algebraic_surface_packing_cutoff (hbez : PaperI.RationalCount.PublishedNonsingularBezout)
    (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (G : Equation), G ≠ 0 → G.totalDegree ≤ D →
      ∀ (c : Plane → ℝ) (U E : Set Plane), IsOpen U → ContDiffOn ℝ 2 c U →
      MeasurableSet E → E ⊆ U →
      (∀ x ∈ U, MvPolynomial.eval (graph c x) G = 0) →
      (∀ x ∈ U, gradient G (graph c x) ≠ 0) →
      ∀ (κ : ℝ), 0 < κ → (∀ x ∈ E, κ ≤ |(hessian c x).det|) →
      ∀ (B : Matrix (Fin 3) (Fin 3) ℝ), B.det ≠ 0 →
      ∀ (b center : Space) (R : ℝ), 0 ≤ R →
      (∀ x ∈ E, (EuclideanSpace.equiv (Fin 3) ℝ).symm (affine B b (graph c) x) ∈
        Metric.closedBall ((EuclideanSpace.equiv (Fin 3) ℝ).symm center) R) →
      volume E ≤ ENNReal.ofReal
        (C * R ^ (3 / 2 : ℝ) * κ ^ (-1 / 4 : ℝ) * |B.det| ^ (-1 / 2 : ℝ)) ∧
      volume E ≠ ∞ ∧
      (volume E).toReal ≤
        C * R ^ (3 / 2 : ℝ) * κ ^ (-1 / 4 : ℝ) * |B.det| ^ (-1 / 2 : ℝ) := by
  let N : ℕ := (max 1 D) ^ 3
  let Ca : ℝ := 12 * (N : ℝ)
  let Ck : ℝ := 12 * ((2 * N : ℕ) : ℝ)
  have hN : 0 < N := pow_pos (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)) _
  have hCa : 0 < Ca := mul_pos (by norm_num) (Nat.cast_pos.mpr hN)
  have hCk : 0 < Ck := mul_pos (by norm_num) (Nat.cast_pos.mpr (Nat.mul_pos (by decide) hN))
  refine ⟨Ck ^ (1 / 4 : ℝ) * Ca ^ (3 / 4 : ℝ),
    mul_pos (Real.rpow_pos_of_pos hCk _) (Real.rpow_pos_of_pos hCa _), ?_⟩
  intro G hG hD c U E hU hc hE hEU hzero hgrad κ hκ hH B hB b center R hR hball
  let σ := affine B b (graph c)
  let P := transformedEquation b B G
  have hσ : ContDiffOn ℝ 2 σ U := affine_contDiffOn B b _ U (graph_contDiffOn c U hc)
  have hσreg : RegularOn σ U := affine_regularOn B hB b _ U hU (graph_contDiffOn c U hc)
    (fun x hx => graph_regular c x ((hc.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)))
  have hσinj : Function.Injective σ := affine_graph_injective B hB b c
  have hP := PaperI.AffineDefiningPolynomial.affine_defining_polynomial_stage b B hB G hG D hD
  have hPdegree : P.totalDegree ≤ D := hP.2.2.1
  have hPzero (x : Plane) (hx : x ∈ U) : MvPolynomial.eval (σ x) P = 0 :=
    (hP.2.2.2.2 (graph c x)).trans (hzero x hx)
  have hPgrad (x : Plane) (hx : x ∈ U) : gradient P (σ x) ≠ 0 :=
    physical_equation_gradient_ne_zero b B hB G (graph c x) (hgrad x hx)
  have ha := chart_area_le_of_projection_fibers σ U E hU hσ hE hEU center R hR
    (fun x hx i => euclidean_ball_coord (hball x hx) i) N
    (surface_projection_fiber_bound hbez D P hPdegree σ U E hU hσ hσreg hσinj hEU hPzero hPgrad)
  have hk := chart_total_curvature_le_of_projection_fibers σ U E hU hσ hσreg hE hEU (2 * N)
    (normal_projection_fiber_bound hbez D P hPdegree σ U E hU hσ hσreg hσinj hEU hPzero hPgrad)
  exact PaperI.AffineCutoffAssembly.affine_surface_cutoff_from_geometric_bounds
    Ck Ca hCk.le hCa.le R hR κ hκ B hB b c U E hU hc hE hEU hH hk ha

end PaperI.AffineArea
