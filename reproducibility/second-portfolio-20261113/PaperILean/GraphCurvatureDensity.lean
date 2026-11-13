import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

open MeasureTheory Matrix Filter
open scoped ENNReal Topology

namespace PaperI.GraphCurvatureDensity

abbrev Plane := Fin 2 → ℝ
abbrev Space := Fin 3 → ℝ

def basis (j : Fin 2) : Plane := Pi.single j 1

def graph (c : Plane → ℝ) (x : Plane) : Space := ![c x, x 0, x 1]

noncomputable def graphD (L : Plane →L[ℝ] ℝ) : Plane →L[ℝ] Space :=
  ContinuousLinearMap.pi ![L, ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1]

noncomputable def coordDeriv (c : Plane → ℝ) (j : Fin 2) (x : Plane) : ℝ :=
  fderiv ℝ c x (basis j)

noncomputable def gradient (c : Plane → ℝ) (x : Plane) : Plane :=
  fun j => coordDeriv c j x

noncomputable def hessian (c : Plane → ℝ) (x : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => fderiv ℝ (coordDeriv c j) x (basis i)

def tangent (a : Plane) (i : Fin 2) : Space := ![a i, basis i 0, basis i 1]

def weight (a : Plane) : ℝ := 1 + a 0 ^ 2 + a 1 ^ 2

noncomputable def normal (a : Plane) : Space :=
  fun j => (![1, -a 0, -a 1] : Space) j / Real.sqrt (weight a)

def firstForm (a : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => dotProduct (tangent a i) (tangent a j)

noncomputable def secondForm (a : Plane) (H : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => dotProduct (normal a) (![H i j, 0, 0] : Space)

noncomputable def curvature (a : Plane) (H : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (secondForm a H).det / (firstForm a).det

noncomputable def areaDensity (a : Plane) : ℝ := Real.sqrt (firstForm a).det

theorem weight_pos (a : Plane) : 0 < weight a := by
  unfold weight
  positivity

theorem firstForm_det (a : Plane) : (firstForm a).det = weight a := by
  simp [Matrix.det_fin_two, firstForm, tangent, basis, dotProduct, Fin.sum_univ_succ, weight]
  ring

theorem secondForm_entry (a : Plane) (H : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    secondForm a H i j = H i j / Real.sqrt (weight a) := by
  simp [secondForm, normal, dotProduct, Fin.sum_univ_succ, div_eq_mul_inv, mul_comm]

theorem secondForm_det (a : Plane) (H : Matrix (Fin 2) (Fin 2) ℝ) :
    (secondForm a H).det = H.det / weight a := by
  have hs : Real.sqrt (weight a) ^ 2 = weight a := Real.sq_sqrt (le_of_lt (weight_pos a))
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [secondForm_entry]
  rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, ← sq, hs]

theorem curvature_eq (a : Plane) (H : Matrix (Fin 2) (Fin 2) ℝ) :
    curvature a H = H.det / weight a ^ 2 := by
  rw [curvature, secondForm_det, firstForm_det, div_div, sq]

theorem normal_unit (a : Plane) : dotProduct (normal a) (normal a) = 1 := by
  have hp := weight_pos a
  have hs : Real.sqrt (weight a) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hsq := Real.sq_sqrt (le_of_lt hp)
  simp [normal, dotProduct, Fin.sum_univ_succ]
  field_simp
  dsimp [weight]
  ring

theorem normal_orthogonal (a : Plane) (i : Fin 2) :
    dotProduct (normal a) (tangent a i) = 0 := by
  fin_cases i <;>
    simp [normal, tangent, basis, dotProduct, Fin.sum_univ_succ, div_eq_mul_inv] <;> ring

theorem curvature_density (a : Plane) (H : Matrix (Fin 2) (Fin 2) ℝ) :
    |curvature a H| ^ (1 / 4 : ℝ) * areaDensity a = |H.det| ^ (1 / 4 : ℝ) := by
  have hp := weight_pos a
  have hp2 : 0 < weight a ^ 2 := sq_pos_of_pos hp
  rw [curvature_eq, abs_div, abs_of_pos hp2, Real.div_rpow (abs_nonneg _) (le_of_lt hp2)]
  have hpow : (weight a ^ 2) ^ (1 / 4 : ℝ) = Real.sqrt (weight a) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hp)]
    norm_num
  rw [hpow, areaDensity, firstForm_det]
  exact div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2 hp))

theorem hasFDerivAt_graph (c : Plane → ℝ) (x : Plane) (L : Plane →L[ℝ] ℝ)
    (hc : HasFDerivAt c L x) : HasFDerivAt (graph c) (graphD L) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hc
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt

theorem graph_tangent (c : Plane → ℝ) (x : Plane) (hc : DifferentiableAt ℝ c x)
    (i : Fin 2) : fderiv ℝ (graph c) x (basis i) = tangent (gradient c x) i := by
  rw [(hasFDerivAt_graph c x _ hc.hasFDerivAt).fderiv]
  ext j
  fin_cases j <;> simp [graphD, tangent, gradient, coordDeriv]

noncomputable def actualFirstForm (c : Plane → ℝ) (x : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => dotProduct (fderiv ℝ (graph c) x (basis i)) (fderiv ℝ (graph c) x (basis j))

noncomputable def actualSecondForm (c : Plane → ℝ) (x : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => dotProduct (normal (gradient c x))
    (fderiv ℝ (fun y => fderiv ℝ (graph c) y (basis j)) x (basis i))

noncomputable def gaussianCurvature (c : Plane → ℝ) (x : Plane) : ℝ :=
  (actualSecondForm c x).det / (actualFirstForm c x).det

noncomputable def graphAreaDensity (c : Plane → ℝ) (x : Plane) : ℝ :=
  Real.sqrt (actualFirstForm c x).det

theorem graph_second_derivative (c : Plane → ℝ) (x : Plane)
    (hc : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ c y)
    (j : Fin 2) (hj : DifferentiableAt ℝ (coordDeriv c j) x) (i : Fin 2) :
    fderiv ℝ (fun y => fderiv ℝ (graph c) y (basis j)) x (basis i) =
      ![hessian c x i j, 0, 0] := by
  let L : Plane →L[ℝ] Space := ContinuousLinearMap.pi
    ![fderiv ℝ (coordDeriv c j) x, 0, 0]
  have hd : HasFDerivAt (fun y => tangent (gradient c y) j) L x := by
    apply hasFDerivAt_pi.mpr
    intro k
    fin_cases k
    · exact hj.hasFDerivAt
    · exact hasFDerivAt_const _ _
    · exact hasFDerivAt_const _ _
  have he : (fun y => fderiv ℝ (graph c) y (basis j)) =ᶠ[𝓝 x]
      (fun y => tangent (gradient c y) j) := by
    filter_upwards [hc] with y hy
    exact graph_tangent c y hy j
  rw [(hd.congr_of_eventuallyEq he).fderiv]
  ext k
  fin_cases k <;> simp [L, hessian]

/-- The full graph calculation, using the actual first and second derivatives.
The local differentiability hypotheses follow from C² regularity on an open chart. -/
theorem graph_curvature_density_stage (c : Plane → ℝ) (x : Plane)
    (hc : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ c y)
    (h2 : ∀ j : Fin 2, DifferentiableAt ℝ (coordDeriv c j) x) :
    (actualFirstForm c x).det = 1 + gradient c x 0 ^ 2 + gradient c x 1 ^ 2 ∧
    graphAreaDensity c x = Real.sqrt (1 + gradient c x 0 ^ 2 + gradient c x 1 ^ 2) ∧
    gaussianCurvature c x = (hessian c x).det /
      (1 + gradient c x 0 ^ 2 + gradient c x 1 ^ 2) ^ 2 ∧
    |gaussianCurvature c x| ^ (1 / 4 : ℝ) * graphAreaDensity c x =
      |(hessian c x).det| ^ (1 / 4 : ℝ) := by
  have hx : DifferentiableAt ℝ c x := hc.self_of_nhds
  have hI : actualFirstForm c x = firstForm (gradient c x) := by
    ext i j
    simp only [actualFirstForm, firstForm, graph_tangent c x hx]
  have hII : actualSecondForm c x = secondForm (gradient c x) (hessian c x) := by
    ext i j
    simp only [actualSecondForm, secondForm, graph_second_derivative c x hc j (h2 j) i]
  have hk : gaussianCurvature c x = curvature (gradient c x) (hessian c x) := by
    rw [gaussianCurvature, hI, hII, curvature]
  have ha : graphAreaDensity c x = areaDensity (gradient c x) := by
    rw [graphAreaDensity, hI, areaDensity]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hI, firstForm_det, weight]
  · rw [ha, areaDensity, firstForm_det, weight]
  · rw [hk, curvature_eq, weight]
  · rw [hk, ha]
    exact curvature_density _ _

/-- Surface area in graph coordinates, defined by the Gram Jacobian of the
actual graph differential. For a parameter domain E use μ = volume.restrict E. -/
noncomputable def graphAreaMeasure (c : Plane → ℝ) (μ : Measure Plane) : Measure Plane :=
  μ.withDensity (fun x => ENNReal.ofReal (graphAreaDensity c x))

/-- The nonnegative integral identity allows infinite area or curvature integrals. -/
theorem graph_curvature_integral (c : Plane → ℝ) (μ : Measure Plane)
    (hc : ∀ᵐ x ∂μ, (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ c y) ∧
      ∀ j : Fin 2, DifferentiableAt ℝ (coordDeriv c j) x)
    (harea : AEMeasurable (fun x => ENNReal.ofReal (graphAreaDensity c x)) μ)
    (hcurv : AEMeasurable (fun x => ENNReal.ofReal (|gaussianCurvature c x| ^ (1 / 4 : ℝ))) μ) :
    (∫⁻ x, ENNReal.ofReal (|gaussianCurvature c x| ^ (1 / 4 : ℝ)) ∂graphAreaMeasure c μ) =
      ∫⁻ x, ENNReal.ofReal (|(hessian c x).det| ^ (1 / 4 : ℝ)) ∂μ := by
  rw [graphAreaMeasure, lintegral_withDensity_eq_lintegral_mul₀ harea hcurv]
  apply lintegral_congr_ae
  filter_upwards [hc] with x hx
  change ENNReal.ofReal (graphAreaDensity c x) *
    ENNReal.ofReal (|gaussianCurvature c x| ^ (1 / 4 : ℝ)) = _
  rw [← ENNReal.ofReal_mul (show 0 ≤ graphAreaDensity c x from Real.sqrt_nonneg _), mul_comm,
    (graph_curvature_density_stage c x hx.1 hx.2).2.2.2]

theorem regularity_on (c : Plane → ℝ) (U : Set Plane) (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 c U) (x : Plane) (hx : x ∈ U) :
    (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ c y) ∧
      ∀ j : Fin 2, DifferentiableAt ℝ (coordDeriv c j) x := by
  constructor
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hc.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  · intro j
    have hd : ContDiffOn ℝ 1 (fderiv ℝ c) U := hc.fderiv_of_isOpen hU (by norm_num)
    have hj : ContDiffOn ℝ 1 (coordDeriv c j) U := hd.clm_apply contDiffOn_const
    exact (hj.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)

theorem densities_continuousOn (c : Plane → ℝ) (U : Set Plane) (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 c U) :
    ContinuousOn (graphAreaDensity c) U ∧ ContinuousOn (gaussianCurvature c) U := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ c) U := hc.fderiv_of_isOpen hU (by norm_num)
  have hj (j : Fin 2) : ContDiffOn ℝ 1 (coordDeriv c j) U :=
    hd.clm_apply contDiffOn_const
  have hg (j : Fin 2) : ContinuousOn (fun x => gradient c x j) U := (hj j).continuousOn
  have hh (i j : Fin 2) : ContinuousOn (fun x => hessian c x i j) U := by
    have h : ContDiffOn ℝ 0 (fderiv ℝ (coordDeriv c j)) U :=
      (hj j).fderiv_of_isOpen hU (by norm_num)
    exact h.continuousOn.clm_apply continuousOn_const
  have hw : ContinuousOn (fun x => weight (gradient c x)) U :=
    (continuousOn_const.add ((hg 0).pow 2)).add ((hg 1).pow 2)
  have hdet : ContinuousOn (fun x => (hessian c x).det) U := by
    simp only [Matrix.det_fin_two]
    exact ((hh 0 0).mul (hh 1 1)).sub ((hh 0 1).mul (hh 1 0))
  constructor
  · apply hw.sqrt.congr
    intro x hx
    exact (graph_curvature_density_stage c x
      (regularity_on c U hU hc x hx).1 (regularity_on c U hU hc x hx).2).2.1
  · apply (hdet.div (hw.pow 2) (fun x _ => ne_of_gt (sq_pos_of_pos (weight_pos _)))).congr
    intro x hx
    exact (graph_curvature_density_stage c x
      (regularity_on c U hU hc x hx).1 (regularity_on c U hU hc x hx).2).2.2.1

/-- I3331-I3334. A C² graph on an open chart, restricted to any measurable
parameter subset, has the claimed pointwise and nonnegative integral identities.
The area measure is expressed in that chart by its actual Gram Jacobian. -/
theorem graph_curvature_area_stage (c : Plane → ℝ) (U E : Set Plane)
    (hU : IsOpen U) (hc : ContDiffOn ℝ 2 c U) (hE : MeasurableSet E) (hEU : E ⊆ U) :
    (∀ x ∈ U,
      (actualFirstForm c x).det = 1 + gradient c x 0 ^ 2 + gradient c x 1 ^ 2 ∧
      graphAreaDensity c x = Real.sqrt (1 + gradient c x 0 ^ 2 + gradient c x 1 ^ 2) ∧
      gaussianCurvature c x = (hessian c x).det /
        (1 + gradient c x 0 ^ 2 + gradient c x 1 ^ 2) ^ 2 ∧
      |gaussianCurvature c x| ^ (1 / 4 : ℝ) * graphAreaDensity c x =
        |(hessian c x).det| ^ (1 / 4 : ℝ)) ∧
    (∫⁻ x, ENNReal.ofReal (|gaussianCurvature c x| ^ (1 / 4 : ℝ))
      ∂graphAreaMeasure c (volume.restrict E)) =
      ∫⁻ x, ENNReal.ofReal (|(hessian c x).det| ^ (1 / 4 : ℝ)) ∂volume.restrict E := by
  constructor
  · intro x hx
    exact graph_curvature_density_stage c x
      (regularity_on c U hU hc x hx).1 (regularity_on c U hU hc x hx).2
  · apply graph_curvature_integral
    · filter_upwards [ae_restrict_mem hE] with x hx
      exact regularity_on c U hU hc x (hEU hx)
    · exact (((densities_continuousOn c U hU hc).1.mono hEU).aemeasurable hE).ennreal_ofReal
    · have hk := ((densities_continuousOn c U hU hc).2.mono hEU).abs
      exact ((hk.rpow_const (fun _ _ => Or.inr (by norm_num))).aemeasurable hE).ennreal_ofReal

end PaperI.GraphCurvatureDensity


