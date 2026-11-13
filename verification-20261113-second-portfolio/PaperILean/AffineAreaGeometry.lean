import PaperILean.AffineSurfaceStage
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Matrix Set Filter
open scoped Topology

namespace PaperI.AffineArea

open PaperI.AffineSurfaceCross hiding Space
open PaperI.AffineSurfaceAlgebra hiding Space
open PaperI.AffineSurfaceDerivatives hiding Plane Space
open PaperI.AffineSurfaceStage

/-- The two coordinates after the omitted coordinate, in cyclic order. -/
def coord (i : Fin 3) (j : Fin 2) : Fin 3 :=
  i + (Fin.castLE (by decide : 2 ≤ 3) j + 1)

def project (i : Fin 3) (u : Space) : Plane := fun j => u (coord i j)

noncomputable def projectCLM (i : Fin 3) : Space →L[ℝ] Plane :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (coord i j))

theorem project_contDiffOn (i : Fin 3) {f : Plane → Space} {U : Set Plane}
    (hf : ContDiffOn ℝ 1 f U) : ContDiffOn ℝ 1 (fun x => project i (f x)) U :=
  (projectCLM i).contDiff.comp_contDiffOn hf

theorem project_fderiv (i : Fin 3) {f : Plane → Space} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (v : Plane) :
    fderiv ℝ (fun x => project i (f x)) x v = project i (fderiv ℝ f x v) := by
  have h := ((projectCLM i).hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => project i (f x)) x = _ at h
  rw [h]
  rfl

theorem project_det (i : Fin 3) {f : Plane → Space} {x : Plane}
    (hf : DifferentiableAt ℝ f x) :
    (fderiv ℝ (fun x => project i (f x)) x).det =
      cross (tangent f 0 x) (tangent f 1 x) i := by
  change LinearMap.det (fderiv ℝ (fun x => project i (f x)) x).toLinearMap = _
  rw [← LinearMap.det_toMatrix']
  have hm (a b : Fin 2) :
      LinearMap.toMatrix' (fderiv ℝ (fun x => project i (f x)) x).toLinearMap a b =
        tangent f b x (coord i a) := by
    rw [LinearMap.toMatrix'_apply]
    change fderiv ℝ (fun x => project i (f x)) x
      (fun j => if j = b then 1 else 0) a = _
    rw [project_fderiv i hf]
    rw [show (fun j : Fin 2 => if j = b then (1 : ℝ) else 0) = basis b by
      ext j
      simp [basis, Pi.single_apply]]
    rfl
  rw [Matrix.det_fin_two, hm, hm, hm, hm]
  fin_cases i <;> simp [coord, cross] <;> ring

theorem length_le_sum_abs (u : Space) :
    length u ≤ ∑ i, |u i| := by
  unfold length
  have h0 := abs_nonneg (u 0)
  have h1 := abs_nonneg (u 1)
  have h2 := abs_nonneg (u 2)
  have hs : 0 ≤ ∑ i, |u i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply (Real.sqrt_le_left hs).mpr
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_abs (u 0), sq_abs (u 1), sq_abs (u 2),
    mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]

theorem cross_dot_cross (a b u w : Space) :
    dotProduct (cross a b) (cross u w) =
      dotProduct a u * dotProduct b w - dotProduct a w * dotProduct b u := by
  simp [cross, dotProduct, Fin.sum_univ_three]
  ring

theorem chart_area_le_projected {σ : Plane → Space} {x : Plane}
    (hσ : DifferentiableAt ℝ σ x) :
    chartAreaDensity σ x ≤ ∑ i, |(fderiv ℝ (fun y => project i (σ y)) x).det| := by
  simp only [project_det _ hσ]
  unfold chartAreaDensity
  rw [area_eq_length]
  exact length_le_sum_abs _

private theorem dot_contDiffOn {f g : Plane → Space} {U : Set Plane}
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    ContDiffOn ℝ 1 (fun x => dotProduct (f x) (g x)) U := by
  have h (i : Fin 3) := (contDiffOn_pi.mp hf i).mul (contDiffOn_pi.mp hg i)
  simpa [dotProduct, Fin.sum_univ_three] using ((h 0).add (h 1)).add (h 2)

theorem tangent_contDiffOn {σ : Plane → Space} {U : Set Plane} (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (j : Fin 2) : ContDiffOn ℝ 1 (tangent σ j) U :=
  (hσ.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const

theorem normal_contDiffOn {σ : Plane → Space} {U : Set Plane} (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (hreg : RegularOn σ U) :
    ContDiffOn ℝ 1 (chartNormal σ) U := by
  let u := tangent σ 0
  let w := tangent σ 1
  have hu := tangent_contDiffOn hU hσ 0
  have hw := tangent_contDiffOn hU hσ 1
  have hx : ContDiffOn ℝ 1 (fun p => cross (u p) (w p)) U := by
    apply contDiffOn_pi.mpr
    intro i
    have h (j k : Fin 3) := (contDiffOn_pi.mp hu j).mul (contDiffOn_pi.mp hw k)
    fin_cases i
    · simpa [cross,u,w] using (h 1 2).sub (h 2 1)
    · simpa [cross,u,w] using (h 2 0).sub (h 0 2)
    · simpa [cross,u,w] using (h 0 1).sub (h 1 0)
  have hd := dot_contDiffOn hx hx
  have hs := hd.sqrt (fun x hx => (hreg x hx).ne')
  have hi := hs.inv (fun x hx => (Real.sqrt_pos.mpr (hreg x hx)).ne')
  unfold chartNormal normal
  simpa only [area, ← cross_dot_self, u, w] using hi.smul hx

private theorem fderiv_dot {f g : Plane → Space} {x v : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => dotProduct (f y) (g y)) x v =
      dotProduct (fderiv ℝ f x v) (g x) + dotProduct (f x) (fderiv ℝ g x v) := by
  have h (i : Fin 3) := ((hasFDerivAt_apply i (f x)).comp x hf.hasFDerivAt).mul
    ((hasFDerivAt_apply i (g x)).comp x hg.hasFDerivAt)
  have hd := ((h 0).add (h 1)).add (h 2)
  simp only [Function.comp_def] at hd
  rw [show (fun y => dotProduct (f y) (g y)) =
    (fun y => (f y 0 * g y 0 + f y 1 * g y 1) + f y 2 * g y 2) by
      funext y; simp [dotProduct, Fin.sum_univ_three]]
  rw [hd.fderiv]
  simp [dotProduct, Fin.sum_univ_three, ContinuousLinearMap.comp_apply]
  ring

theorem normal_deriv_tangent {σ : Plane → Space} {U : Set Plane} (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (hreg : RegularOn σ U) {x : Plane} (hx : x ∈ U)
    (v : Plane) :
    dotProduct (fderiv ℝ (chartNormal σ) x v) (chartNormal σ x) = 0 := by
  have hd := ((normal_contDiffOn hU hσ hreg).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have he : (fun _ : Plane => (1 : ℝ)) =ᶠ[𝓝 x]
      fun y => dotProduct (chartNormal σ y) (chartNormal σ y) := by
    filter_upwards [hU.mem_nhds hx] with y hy using
      (normal_unit _ _ (hreg y hy)).symm
  have hf := ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).congr_of_eventuallyEq he.symm).fderiv
  have h := fderiv_dot (v := v) hd hd
  rw [hf, ContinuousLinearMap.zero_apply, dotProduct_comm (chartNormal σ x)] at h
  linarith

private theorem normal_second_form {σ : Plane → Space} {U : Set Plane} (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (hreg : RegularOn σ U) {x : Plane} (hx : x ∈ U)
    (i j : Fin 2) :
    dotProduct (tangent (chartNormal σ) i x) (tangent σ j x) =
      -secondForm (chartNormal σ x) (secondDerivative σ x) i j := by
  have hd := ((normal_contDiffOn hU hσ hreg).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hj := ((tangent_contDiffOn hU hσ j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have he : (fun _ : Plane => (0 : ℝ)) =ᶠ[𝓝 x]
      fun y => dotProduct (chartNormal σ y) (tangent σ j y) := by
    filter_upwards [hU.mem_nhds hx] with y _
    fin_cases j
    · exact (normal_left _ _).symm
    · exact (normal_right _ _).symm
  have hf := ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).congr_of_eventuallyEq he.symm).fderiv
  have h := fderiv_dot (v := basis i) hd hj
  rw [hf, ContinuousLinearMap.zero_apply] at h
  change dotProduct (fderiv ℝ (chartNormal σ) x (basis i)) (tangent σ j x) =
    -dotProduct (chartNormal σ x) (fderiv ℝ (tangent σ j) x (basis i))
  linarith

private theorem abs_dot_unit_le_length {v n : Space} (hn : dotProduct n n = 1) :
    |dotProduct v n| ≤ length v := by
  unfold length
  apply (Real.le_sqrt (abs_nonneg _) (dot_self_nonneg _)).mpr
  rw [sq_abs]
  have h := dot_self_nonneg (v - (dotProduct v n) • n)
  simp only [sub_dotProduct, dotProduct_sub, dot_smul_left, dot_smul_right,
    hn, mul_one, dotProduct_comm n v] at h
  nlinarith

theorem chart_curvature_area_le_projected {σ : Plane → Space} {U : Set Plane}
    (hU : IsOpen U) (hσ : ContDiffOn ℝ 2 σ U) (hreg : RegularOn σ U)
    {x : Plane} (hx : x ∈ U) :
    |chartCurvature σ (chartNormal σ) x| * chartAreaDensity σ x ≤
      ∑ i, |(fderiv ℝ (fun y => project i (chartNormal σ y)) x).det| := by
  let u := tangent σ 0 x
  let w := tangent σ 1 x
  let n := chartNormal σ x
  let a := tangent (chartNormal σ) 0 x
  let b := tangent (chartNormal σ) 1 x
  let II := secondForm n (secondDerivative σ x)
  have hu : dotProduct n n = 1 := normal_unit _ _ (hreg x hx)
  have ha : 0 < area u w := area_pos _ _ (hreg x hx)
  have hd : dotProduct (cross a b) (cross u w) = II.det := by
    rw [cross_dot_cross, Matrix.det_fin_two]
    rw [normal_second_form hU hσ hreg hx 0 0, normal_second_form hU hσ hreg hx 1 1,
      normal_second_form hU hσ hreg hx 0 1, normal_second_form hU hσ hreg hx 1 0]
    dsimp [II, n]
    ring
  have hn : cross u w = area u w • n := by
    change cross u w = area u w • ((area u w)⁻¹ • cross u w)
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have he : |chartCurvature σ (chartNormal σ) x| * chartAreaDensity σ x =
      |dotProduct (cross a b) n| := by
    change |II.det / (gram u w).det| * area u w = _
    rw [← hd, hn, dot_smul_right, ← area_sq, abs_div, abs_mul,
      abs_of_pos ha, abs_of_pos (pow_pos ha 2)]
    field_simp
    ring
  have hnD := ((normal_contDiffOn hU hσ hreg).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  rw [he]
  simp only [project_det _ hnD]
  exact (abs_dot_unit_le_length hu).trans (length_le_sum_abs _)

end PaperI.AffineArea
