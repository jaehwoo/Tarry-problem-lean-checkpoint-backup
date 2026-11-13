import PaperILean.AffineAreaGeometry
import PaperILean.RationalCount

open Matrix MvPolynomial Filter Set
open scoped Topology

namespace PaperI.AffineArea

open PaperI.AffineSurfaceCross hiding Space
open PaperI.AffineSurfaceAlgebra hiding Space
open PaperI.AffineSurfaceDerivatives hiding Space Plane
open PaperI.AffineSurfaceStage
open PaperI.RationalCount

abbrev Equation := MvPolynomial (Fin 3) ℝ

noncomputable def gradient (G : Equation) (x : Space) : Space := fun i =>
  MvPolynomial.eval x (MvPolynomial.pderiv i G)

theorem gradient_contDiff (G : Equation) : ContDiff ℝ 1 (gradient G) :=
  contDiff_pi.mpr (fun i => polynomial_contDiff (MvPolynomial.pderiv i G) 1)

theorem differential_eq_gradient_dot (G : Equation) (x v : Space) :
    polynomialDifferential G x v = dotProduct (gradient G x) v := by
  rw [polynomialDifferential_apply]
  rfl

theorem polynomial_fderiv_eq_gradient_dot (G : Equation) (x v : Space) :
    fderiv ℝ (fun y => MvPolynomial.eval y G) x v = dotProduct (gradient G x) v := by
  rw [(polynomial_hasFDerivAt G x).fderiv]
  exact differential_eq_gradient_dot G x v

private theorem mulVec_injective_of_det_ne_zero {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ}
    (hM : M.det ≠ 0) : Function.Injective M.mulVec :=
  Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hM))

private theorem dotVec_injective_of_unit_normal {n u w : Space}
    (h : dotProduct n (cross u w) ≠ 0) :
    Function.Injective (fun v : Space => ![dotProduct n v, dotProduct u v, dotProduct w v]) := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := ![n,u,w]
  have hM : M.det ≠ 0 := by
    have he : M.det = dotProduct n (cross u w) := by
      simp [M, Matrix.det_fin_three, cross, dotProduct, Fin.sum_univ_three]
      ring
    rwa [he]
  intro a b hab
  apply mulVec_injective_of_det_ne_zero hM
  ext i
  fin_cases i
  · simpa [M, Matrix.mulVec] using congrFun hab (0 : Fin 3)
  · simpa [M, Matrix.mulVec] using congrFun hab (1 : Fin 3)
  · simpa [M, Matrix.mulVec] using congrFun hab (2 : Fin 3)

theorem cross_eq_area_smul_normal {u w : Space}
    (hreg : 0 < dotProduct (cross u w) (cross u w)) :
    cross u w = area u w • normal u w := by
  rw [normal, smul_smul, mul_inv_cancel₀ (area_pos u w hreg).ne', one_smul]

private theorem dot_normal_cross_ne_zero {u w : Space}
    (hreg : 0 < dotProduct (cross u w) (cross u w)) :
    dotProduct (normal u w) (cross u w) ≠ 0 := by
  rw [normal, dot_smul_left]
  exact mul_ne_zero (inv_ne_zero (area_pos u w hreg).ne') hreg.ne'

theorem eq_smul_normal {u w v : Space}
    (hreg : 0 < dotProduct (cross u w) (cross u w))
    (hvu : dotProduct v u = 0) (hvw : dotProduct v w = 0) :
    v = dotProduct v (normal u w) • normal u w := by
  apply (dotVec_injective_of_unit_normal (dot_normal_cross_ne_zero hreg))
  have hl := normal_left u w
  have hr := normal_right u w
  have hn := normal_unit u w hreg
  simp [dot_smul_right, hn, dotProduct_comm u (normal u w),
    dotProduct_comm w (normal u w), hl, hr, dotProduct_comm u v,
    dotProduct_comm w v, hvu, hvw, dotProduct_comm (normal u w) v]

theorem gradient_annihilates_chart {σ : Plane → Space} {U : Set Plane}
    (hU : IsOpen U) (hσ : ContDiffOn ℝ 2 σ U) (G : Equation)
    (hzero : ∀ x ∈ U, MvPolynomial.eval (σ x) G = 0) {x : Plane} (hx : x ∈ U)
    (v : Plane) :
    dotProduct (gradient G (σ x)) (fderiv ℝ σ x v) = 0 := by
  have hd := ((hσ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
  have hcomp := (polynomial_hasFDerivAt G (σ x)).comp x hd
  have he : (fun y => MvPolynomial.eval (σ y) G) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy using hzero y hy
  have hf := (hcomp.congr_of_eventuallyEq he.symm).fderiv
  simp only [fderiv_const] at hf
  have hh := congrArg (fun L : Plane →L[ℝ] ℝ => L v) hf
  change (0 : Plane →L[ℝ] ℝ) v = polynomialDifferential G (σ x) (fderiv ℝ σ x v) at hh
  rw [ContinuousLinearMap.zero_apply] at hh
  exact (differential_eq_gradient_dot _ _ _).symm.trans hh.symm

theorem gradient_parallel {σ : Plane → Space} {U : Set Plane}
    (hU : IsOpen U) (hσ : ContDiffOn ℝ 2 σ U) (hreg : RegularOn σ U)
    (G : Equation) (hzero : ∀ x ∈ U, MvPolynomial.eval (σ x) G = 0) {x : Plane} (hx : x ∈ U) :
    gradient G (σ x) =
      dotProduct (gradient G (σ x)) (chartNormal σ x) • chartNormal σ x :=
  eq_smul_normal (hreg x hx) (gradient_annihilates_chart hU hσ G hzero hx (basis 0))
    (gradient_annihilates_chart hU hσ G hzero hx (basis 1))

private theorem fderiv_eq_tangent_sum (σ : Plane → Space) (x v : Plane) :
    fderiv ℝ σ x v = v 0 • tangent σ 0 x + v 1 • tangent σ 1 x := by
  conv_lhs =>
    rw [show v = v 0 • basis 0 + v 1 • basis 1 by
      ext j
      fin_cases j <;> simp [basis, Pi.single_apply]]
  simp [tangent]

private theorem coordinate_triple (i k : Fin 3) :
    k = i ∨ k = coord i 0 ∨ k = coord i 1 := by
  fin_cases i <;> fin_cases k <;> decide

private theorem dot_zero_project_zero {i : Fin 3} {n v : Space}
    (hi : n i ≠ 0) (hn : dotProduct n v = 0) (hp : project i v = 0) : v = 0 := by
  have h0 : v (coord i 0) = 0 := congrFun hp 0
  have h1 : v (coord i 1) = 0 := congrFun hp 1
  have he : n i * v i = 0 := by
    fin_cases i <;> simp [dotProduct, Fin.sum_univ_three, coord] at h0 h1 hn ⊢ <;>
      simpa [h0,h1] using hn
  ext j
  rcases coordinate_triple i j with rfl | rfl | rfl
  · exact (mul_eq_zero.mp he).resolve_left hi
  · exact h0
  · exact h1

private theorem fderiv_project_injective {i : Fin 3} {σ : Plane → Space} {x : Plane}
    (hdet : (fderiv ℝ (fun x => project i (σ x)) x).det ≠ 0) :
    Function.Injective (fderiv ℝ (fun x => project i (σ x)) x) := by
  let A := fderiv ℝ (fun x => project i (σ x)) x
  let M := LinearMap.toMatrix' A.toLinearMap
  have hM : M.det ≠ 0 := by
    rwa [LinearMap.det_toMatrix']
  have he (v : Plane) : M.mulVec v = A v := by
    have hf : M.toLin' = A.toLinearMap := LinearMap.toMatrix'.symm_apply_apply _
    exact congrArg (fun l : Plane →ₗ[ℝ] Plane => l v) hf
  intro v w hv
  apply mulVec_injective_of_det_ne_zero hM
  rw [he,he]
  exact hv

private theorem tangent_preimage {i : Fin 3} {σ : Plane → Space} {x : Plane} {v : Space}
    (hreg : 0 < dotProduct (cross (tangent σ 0 x) (tangent σ 1 x))
      (cross (tangent σ 0 x) (tangent σ 1 x)))
    (hi : chartNormal σ x i ≠ 0) (hv : dotProduct (chartNormal σ x) v = 0) :
    ∃ a : Plane, fderiv ℝ σ x a = v := by
  let u := tangent σ 0 x
  let w := tangent σ 1 x
  let n := chartNormal σ x
  let j := coord i 0
  let k := coord i 1
  let J := u j * w k - u k * w j
  have hJ : J ≠ 0 := by
    have he : J = cross u w i := by fin_cases i <;> rfl
    rw [he, cross_eq_area_smul_normal hreg]
    exact mul_ne_zero (area_pos _ _ hreg).ne' hi
  let a : Plane := ![(v j * w k - v k * w j)/J, (u j * v k - u k * v j)/J]
  refine ⟨a, sub_eq_zero.mp ?_⟩
  rw [fderiv_eq_tangent_sum]
  apply dot_zero_project_zero hi
  · rw [dotProduct_sub, dotProduct_add, dot_smul_right, dot_smul_right]
    simpa [u, w, chartNormal, normal_left, normal_right] using hv
  · ext l
    fin_cases l
    · change ((v j * w k - v k * w j)/J) * u j +
        ((u j * v k - u k * v j)/J) * w j - v j = 0
      field_simp [J]
      ring
    · change ((v j * w k - v k * w j)/J) * u k +
        ((u j * v k - u k * v j)/J) * w k - v k = 0
      field_simp [J]
      ring

private theorem totalDegree_pderiv_le (G : Equation) (i : Fin 3) :
    (MvPolynomial.pderiv i G).totalDegree ≤ G.totalDegree := by
  classical
  conv_lhs => rw [G.as_sum]
  rw [map_sum]
  have hmon (m : Fin 3 →₀ ℕ) (hm : m ∈ G.support) :
      (MvPolynomial.pderiv i (MvPolynomial.monomial m (G.coeff m))).totalDegree ≤ G.totalDegree := by
    rw [MvPolynomial.pderiv_monomial]
    by_cases hz : G.coeff m * ↑(m i) = 0
    · simp [hz]
    · rw [MvPolynomial.totalDegree_monomial _ hz]
      exact (Finsupp.sum_le_sum_index (tsub_le_self : m - Finsupp.single i 1 ≤ m)
        (fun _ _ => monotone_id) (fun _ _ => rfl)).trans (MvPolynomial.le_totalDegree hm)
  generalize G.support = s at hmon ⊢
  induction s using Finset.induction_on with
  | empty => simp
  | @insert m s hm ih =>
    rw [Finset.sum_insert hm]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le
      (hmon m (Finset.mem_insert_self _ _)) (ih fun k hk => hmon k (Finset.mem_insert_of_mem hk)))

private theorem polynomial_det_ne_zero_of_kernel
    (Q : Fin 3 → Equation) (x : Space)
    (hk : ∀ v : Space, (∀ l, polynomialDifferential (Q l) x v = 0) → v = 0) :
    (polynomialJacobian Q x).det ≠ 0 := by
  intro hz
  obtain ⟨v,hv,hvzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  apply hv
  apply hk v
  rw [polynomialJacobian_mulVec] at hvzero
  exact fun l => congrFun hvzero l

private theorem finite_roots_encard (hbez : PublishedNonsingularBezout)
    (D : ℕ) (Q : Fin 3 → Equation) (hQ : ∀ l, (Q l).totalDegree ≤ max 1 D)
    (σ : Plane → Space) (hσ : Function.Injective σ) (S : Set Plane)
    (hS : ∀ x ∈ S, (∀ l, MvPolynomial.eval (σ x) (Q l) = 0) ∧
      (polynomialJacobian Q (σ x)).det ≠ 0) :
    S.encard ≤ (max 1 D) ^ 3 := by
  obtain ⟨s,hs,hcard⟩ := hbez.bounded_roots 3 (max 1 D) (by decide)
    (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)) Q hQ
  have hsub : σ '' S ⊆ (↑s : Set Space) := by
    rintro y ⟨x,hx,rfl⟩
    exact (hs _).mpr (hS x hx)
  rw [← hσ.encard_image S]
  exact (Set.encard_le_encard hsub).trans
    (by simpa only [Set.encard_coe_eq_coe_finsetCard] using (ENat.coe_le_coe.mpr hcard))

private theorem normal_coord_ne_zero_of_projection {i : Fin 3} {σ : Plane → Space}
    {x : Plane}
    (hreg : 0 < dotProduct (cross (tangent σ 0 x) (tangent σ 1 x))
      (cross (tangent σ 0 x) (tangent σ 1 x)))
    (hd : DifferentiableAt ℝ σ x)
    (hp : (fderiv ℝ (fun x => project i (σ x)) x).det ≠ 0) :
    chartNormal σ x i ≠ 0 := by
  rw [project_det i hd, cross_eq_area_smul_normal hreg] at hp
  exact (mul_ne_zero_iff.mp hp).2

private theorem coordinate_poly_differential (i : Fin 3) (a : ℝ) (x v : Space) :
    polynomialDifferential (MvPolynomial.X i - MvPolynomial.C a) x v = v i := by
  rw [polynomialDifferential_apply]
  simp [MvPolynomial.pderiv_X, MvPolynomial.pderiv_C, Pi.single_apply]

theorem surface_projection_fiber_bound (hbez : PublishedNonsingularBezout)
    (D : ℕ) (G : Equation) (hG : G.totalDegree ≤ D)
    (σ : Plane → Space) (U E : Set Plane) (hU : IsOpen U) (hσ : ContDiffOn ℝ 2 σ U)
    (hreg : RegularOn σ U) (hinj : Function.Injective σ) (hEU : E ⊆ U)
    (hzero : ∀ x ∈ U, MvPolynomial.eval (σ x) G = 0)
    (hgrad : ∀ x ∈ U, gradient G (σ x) ≠ 0)
    (i : Fin 3) (y : Plane) :
    {x | x ∈ E ∧ (fderiv ℝ (fun x => project i (σ x)) x).det ≠ 0 ∧
      project i (σ x) = y}.encard ≤ (max 1 D) ^ 3 := by
  let Q : Fin 3 → Equation := ![G,MvPolynomial.X (coord i 0) - MvPolynomial.C (y 0),
    MvPolynomial.X (coord i 1) - MvPolynomial.C (y 1)]
  refine finite_roots_encard hbez D Q ?_ σ hinj _ ?_
  · intro l
    fin_cases l
    · exact hG.trans (le_max_right _ _)
    · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
    · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  · intro x hx
    have hxu := hEU hx.1
    have hd := ((hσ.contDiffAt (hU.mem_nhds hxu)).differentiableAt (by norm_num))
    have hi := normal_coord_ne_zero_of_projection (hreg x hxu) hd hx.2.1
    have hn := gradient_parallel hU hσ hreg G hzero hxu
    let a := dotProduct (gradient G (σ x)) (chartNormal σ x)
    have ha : a ≠ 0 := by
      intro hz
      apply hgrad x hxu
      exact hn.trans (by rw [show dotProduct (gradient G (σ x)) (chartNormal σ x) = a from rfl,
        hz, zero_smul])
    refine ⟨?_, polynomial_det_ne_zero_of_kernel Q (σ x) ?_⟩
    · intro l
      fin_cases l
      · exact hzero x hxu
      · simpa [Q, project] using sub_eq_zero.mpr (congrFun hx.2.2 (0 : Fin 2))
      · simpa [Q, project] using sub_eq_zero.mpr (congrFun hx.2.2 (1 : Fin 2))
    · intro v hv
      apply dot_zero_project_zero hi
      · have h := hv 0
        change polynomialDifferential G (σ x) v = 0 at h
        rw [differential_eq_gradient_dot, hn, dot_smul_left] at h
        exact (mul_eq_zero.mp h).resolve_left ha
      · ext l
        fin_cases l
        · simpa [Q, project, coordinate_poly_differential] using hv (1 : Fin 3)
        · simpa [Q, project, coordinate_poly_differential] using hv (2 : Fin 3)

private theorem dot_coord_sum (i : Fin 3) (a b : Space) :
    dotProduct a b = a i * b i + a (coord i 0) * b (coord i 0) +
      a (coord i 1) * b (coord i 1) := by
  fin_cases i <;> simp [coord, dotProduct, Fin.sum_univ_three] <;> ring

private theorem cross_coord_det (i : Fin 3) (a b : Space) :
    cross a b i = a (coord i 0) * b (coord i 1) - a (coord i 1) * b (coord i 0) := by
  fin_cases i <;> rfl

private theorem unit_normal_coordinate_nonzero_of_project_det
    {σ : Plane → Space} {U : Set Plane} (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (hreg : RegularOn σ U)
    {x : Plane} (hx : x ∈ U) {i : Fin 3}
    (hp : (fderiv ℝ (fun y => project i (chartNormal σ y)) x).det ≠ 0) :
    chartNormal σ x i ≠ 0 := by
  let n := chartNormal σ x
  let a := tangent (chartNormal σ) 0 x
  let b := tangent (chartNormal σ) 1 x
  have hd := ((normal_contDiffOn hU hσ hreg).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  rw [project_det i hd] at hp
  change cross a b i ≠ 0 at hp
  have hna : dotProduct n a = 0 := by
    rw [dotProduct_comm]
    exact normal_deriv_tangent hU hσ hreg hx (basis 0)
  have hnb : dotProduct n b = 0 := by
    rw [dotProduct_comm]
    exact normal_deriv_tangent hU hσ hreg hx (basis 1)
  have hnn : dotProduct n n = 1 := normal_unit _ _ (hreg x hx)
  intro hz
  change n i = 0 at hz
  rw [dot_coord_sum i] at hna hnb hnn
  simp only [hz, zero_mul, zero_add] at hna hnb hnn
  apply hp
  rw [cross_coord_det]
  have hcases : n (coord i 0) ≠ 0 ∨ n (coord i 1) ≠ 0 := by
    by_contra! hz
    simp [hz.1,hz.2] at hnn
  rcases hcases with hj | hk
  · apply (mul_eq_zero.mp ?_).resolve_left hj
    linear_combination b (coord i 1) * hna - a (coord i 1) * hnb
  · apply (mul_eq_zero.mp ?_).resolve_left hk
    linear_combination a (coord i 0) * hnb - b (coord i 0) * hna

private noncomputable def gradientRow (G : Equation) (n : Space) (i j : Fin 3) : Equation :=
  MvPolynomial.C (n i) * MvPolynomial.pderiv j G -
    MvPolynomial.C (n j) * MvPolynomial.pderiv i G

private theorem gradientRow_degree (G : Equation) (n : Space) (i j : Fin 3) :
    (gradientRow G n i j).totalDegree ≤ G.totalDegree := by
  unfold gradientRow
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simpa only [MvPolynomial.smul_eq_C_mul] using
      (MvPolynomial.totalDegree_smul_le (n i) _).trans (totalDegree_pderiv_le G j)
  · simpa only [MvPolynomial.smul_eq_C_mul] using
      (MvPolynomial.totalDegree_smul_le (n j) _).trans (totalDegree_pderiv_le G i)

private theorem eval_gradientRow (G : Equation) (n : Space) (i j : Fin 3) (x : Space) :
    MvPolynomial.eval x (gradientRow G n i j) =
      n i * gradient G x j - n j * gradient G x i := by
  simp [gradientRow, gradient]

private theorem gradientRow_tangent_differential {σ : Plane → Space} {U : Set Plane}
    (hU : IsOpen U) (hσ : ContDiffOn ℝ 2 σ U) (hreg : RegularOn σ U)
    (G : Equation) (hzero : ∀ x ∈ U, MvPolynomial.eval (σ x) G = 0)
    {x : Plane} (hx : x ∈ U) (i j : Fin 3) (v : Plane) :
    let n := chartNormal σ x
    let a := dotProduct (gradient G (σ x)) n
    let dn := fderiv ℝ (chartNormal σ) x v
    polynomialDifferential (gradientRow G n i j) (σ x) (fderiv ℝ σ x v) =
      a * (n i * dn j - n j * dn i) := by
  dsimp only
  let n := chartNormal σ x
  let a : Plane → ℝ := fun y => dotProduct (gradient G (σ y)) (chartNormal σ y)
  let g : Plane → ℝ := fun y => n i * chartNormal σ y j - n j * chartNormal σ y i
  have hdn := ((normal_contDiffOn hU hσ hreg).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hds := ((hσ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
  have hda : DifferentiableAt ℝ a x := by
    have hdg := ((gradient_contDiff G).differentiable (by norm_num) (σ x)).comp x hds
    have h (l : Fin 3) := ((differentiableAt_apply l (gradient G (σ x))).comp x hdg).mul
      ((differentiableAt_apply l (chartNormal σ x)).comp x hdn)
    unfold a
    simpa only [dotProduct, Fin.sum_univ_three, Function.comp_def] using
      ((h 0).add (h 1)).add (h 2)
  have hdg := (((hasFDerivAt_apply j (chartNormal σ x)).comp x hdn.hasFDerivAt).const_mul
    (n i)).sub (((hasFDerivAt_apply i (chartNormal σ x)).comp x hdn.hasFDerivAt).const_mul (n j))
  have hprod := hda.hasFDerivAt.mul hdg
  have he : (fun y => MvPolynomial.eval (σ y) (gradientRow G n i j)) =ᶠ[𝓝 x] fun y => a y * g y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [eval_gradientRow, gradient_parallel hU hσ hreg G hzero hy]
    change n i * (a y * chartNormal σ y j) - n j * (a y * chartNormal σ y i) = _
    unfold g
    ring
  have hfun := ((polynomial_hasFDerivAt (gradientRow G n i j) (σ x)).comp x
    hds.hasFDerivAt).congr_of_eventuallyEq he.symm
  have h := congrArg (fun L : Plane →L[ℝ] ℝ => L v) (hfun.fderiv.symm.trans hprod.fderiv)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.one_apply, Function.comp_def] at h
  have hgz : g x = 0 := by simp [g,n,mul_comm]
  change _ = _ + g x * _ at h
  rw [hgz, zero_mul, add_zero] at h
  exact h

private theorem killed_by_normal_rows {n v : Space} {i : Fin 3}
    (hi : n i ≠ 0) (hn : dotProduct n n = 1) (hv : dotProduct n v = 0)
    (hrows : ∀ j : Fin 2, n i * v (coord i j) - n (coord i j) * v i = 0) :
    v = 0 := by
  let a := v i / n i
  have he : v = a • n := by
    ext k
    rcases coordinate_triple i k with hk | hk | hk
    · subst k
      change v i = v i / n i * n i
      field_simp
    · subst k
      change v (coord i 0) = v i / n i * n (coord i 0)
      field_simp
      linear_combination hrows 0
    · subst k
      change v (coord i 1) = v i / n i * n (coord i 1)
      field_simp
      linear_combination hrows 1
  rw [he, dot_smul_right, hn, mul_one] at hv
  rw [he, hv, zero_smul]

private theorem fixed_normal_fiber_bound (hbez : PublishedNonsingularBezout)
    (D : ℕ) (G : Equation) (hG : G.totalDegree ≤ D)
    (σ : Plane → Space) (U E : Set Plane) (hU : IsOpen U) (hσ : ContDiffOn ℝ 2 σ U)
    (hreg : RegularOn σ U) (hinj : Function.Injective σ) (hEU : E ⊆ U)
    (hzero : ∀ x ∈ U, MvPolynomial.eval (σ x) G = 0)
    (hgrad : ∀ x ∈ U, gradient G (σ x) ≠ 0)
    (i : Fin 3) (n : Space) :
    {x | x ∈ E ∧ (fderiv ℝ (fun x => project i (chartNormal σ x)) x).det ≠ 0 ∧
      chartNormal σ x = n}.encard ≤ (max 1 D) ^ 3 := by
  let Q : Fin 3 → Equation := ![G,gradientRow G n i (coord i 0),gradientRow G n i (coord i 1)]
  refine finite_roots_encard hbez D Q ?_ σ hinj _ ?_
  · intro l
    fin_cases l
    · exact hG.trans (le_max_right _ _)
    · exact (gradientRow_degree G n i _).trans (hG.trans (le_max_right _ _))
    · exact (gradientRow_degree G n i _).trans (hG.trans (le_max_right _ _))
  · intro x hx
    have hxu := hEU hx.1
    have hn0 : chartNormal σ x = n := hx.2.2
    have hn := gradient_parallel hU hσ hreg G hzero hxu
    let a := dotProduct (gradient G (σ x)) (chartNormal σ x)
    have ha : a ≠ 0 := by
      intro hz
      apply hgrad x hxu
      exact hn.trans (by rw [show dotProduct (gradient G (σ x)) (chartNormal σ x) = a from rfl,
        hz, zero_smul])
    have hi := unit_normal_coordinate_nonzero_of_project_det hU hσ hreg hxu hx.2.1
    have hdn := ((normal_contDiffOn hU hσ hreg).contDiffAt (hU.mem_nhds hxu)).differentiableAt (by norm_num)
    have hunit : dotProduct (chartNormal σ x) (chartNormal σ x) = 1 :=
      normal_unit _ _ (hreg x hxu)
    refine ⟨?_, polynomial_det_ne_zero_of_kernel Q (σ x) ?_⟩
    · intro l
      fin_cases l
      · exact hzero x hxu
      · change MvPolynomial.eval (σ x) (gradientRow G n i (coord i 0)) = 0
        rw [eval_gradientRow, hn, ← hn0]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      · change MvPolynomial.eval (σ x) (gradientRow G n i (coord i 1)) = 0
        rw [eval_gradientRow, hn, ← hn0]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
    · intro v hv
      have ht : dotProduct (chartNormal σ x) v = 0 := by
        have h := hv 0
        change polynomialDifferential G (σ x) v = 0 at h
        rw [differential_eq_gradient_dot, hn, dot_smul_left] at h
        exact (mul_eq_zero.mp h).resolve_left ha
      obtain ⟨u,hu⟩ := tangent_preimage (hreg x hxu) hi ht
      let dn := fderiv ℝ (chartNormal σ) x u
      have hdnt : dotProduct (chartNormal σ x) dn = 0 := by
        rw [dotProduct_comm]
        exact normal_deriv_tangent hU hσ hreg hxu u
      have hrows (j : Fin 2) :
          chartNormal σ x i * dn (coord i j) - chartNormal σ x (coord i j) * dn i = 0 := by
        have h := gradientRow_tangent_differential hU hσ hreg G hzero hxu i (coord i j) u
        dsimp only at h
        rw [hu, hn0] at h
        have hh : polynomialDifferential (gradientRow G n i (coord i j)) (σ x) v = 0 := by
          fin_cases j
          · exact hv 1
          · exact hv 2
        rw [hh] at h
        have hz := h.symm
        rw [← hn0] at hz
        exact (mul_eq_zero.mp hz).resolve_left ha
      have hdn0 := killed_by_normal_rows hi hunit hdnt hrows
      have hproj : fderiv ℝ (fun y => project i (chartNormal σ y)) x u = 0 := by
        rw [project_fderiv i hdn]
        change project i dn = 0
        rw [hdn0]
        rfl
      have hz := fderiv_project_injective hx.2.1
        (show fderiv ℝ (fun y => project i (chartNormal σ y)) x u =
          fderiv ℝ (fun y => project i (chartNormal σ y)) x 0 by simpa using hproj)
      simpa [hz] using hu.symm

private theorem unit_project_completion (i : Fin 3) (y : Plane) :
    ∃ np nm : Space, ∀ n : Space, dotProduct n n = 1 → project i n = y →
      n = np ∨ n = nm := by
  let s := Real.sqrt (1 - y 0 ^ 2 - y 1 ^ 2)
  let mk (a : ℝ) (j : Fin 3) : ℝ :=
    if j = i then a else if j = coord i 0 then y 0 else y 1
  refine ⟨mk s,mk (-s),fun n hn hp => ?_⟩
  have hj : n (coord i 0) = y 0 := congrFun hp 0
  have hk : n (coord i 1) = y 1 := congrFun hp 1
  rw [dot_coord_sum i, hj, hk] at hn
  have hsq : n i ^ 2 = 1 - y 0 ^ 2 - y 1 ^ 2 := by nlinarith
  have hs : s ^ 2 = n i ^ 2 := by
    unfold s
    rw [← hsq, Real.sq_sqrt (sq_nonneg _)]
  have hsign : n i = s ∨ n i = -s := by
    have hprod : (n i - s) * (n i + s) = 0 := by nlinarith only [hs]
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hmk {a : ℝ} (ha : n i = a) : n = mk a := by
    ext j
    rcases coordinate_triple i j with rfl | rfl | rfl
    · simpa [mk] using ha
    · have hni : coord i 0 ≠ i := by fin_cases i <;> decide
      simpa [mk, hni] using hj
    · have hni : coord i 1 ≠ i := by fin_cases i <;> decide
      have hne : coord i 1 ≠ coord i 0 := by fin_cases i <;> decide
      simpa [mk, hni, hne] using hk
  exact hsign.imp hmk hmk

theorem normal_projection_fiber_bound (hbez : PublishedNonsingularBezout)
    (D : ℕ) (G : Equation) (hG : G.totalDegree ≤ D)
    (σ : Plane → Space) (U E : Set Plane) (hU : IsOpen U) (hσ : ContDiffOn ℝ 2 σ U)
    (hreg : RegularOn σ U) (hinj : Function.Injective σ) (hEU : E ⊆ U)
    (hzero : ∀ x ∈ U, MvPolynomial.eval (σ x) G = 0)
    (hgrad : ∀ x ∈ U, gradient G (σ x) ≠ 0)
    (i : Fin 3) (y : Plane) :
    {x | x ∈ E ∧ (fderiv ℝ (fun x => project i (chartNormal σ x)) x).det ≠ 0 ∧
      project i (chartNormal σ x) = y}.encard ≤ (2 * (max 1 D) ^ 3 : ℕ) := by
  obtain ⟨np,nm,hn⟩ := unit_project_completion i y
  let S (n : Space) := {x | x ∈ E ∧
    (fderiv ℝ (fun x => project i (chartNormal σ x)) x).det ≠ 0 ∧ chartNormal σ x = n}
  have hf (n : Space) : (S n).encard ≤ (max 1 D) ^ 3 :=
    fixed_normal_fiber_bound hbez D G hG σ U E hU hσ hreg hinj hEU hzero hgrad i n
  have hsub :
      {x | x ∈ E ∧ (fderiv ℝ (fun x => project i (chartNormal σ x)) x).det ≠ 0 ∧
      project i (chartNormal σ x) = y} ⊆ S np ∪ S nm := by
    intro x hx
    have hu : dotProduct (chartNormal σ x) (chartNormal σ x) = 1 :=
      normal_unit _ _ (hreg x (hEU hx.1))
    exact (hn (chartNormal σ x) hu hx.2.2).imp
      (fun h => ⟨hx.1,hx.2.1,h⟩) (fun h => ⟨hx.1,hx.2.1,h⟩)
  apply (Set.encard_le_encard hsub).trans
  apply (Set.encard_union_le _ _).trans
  simpa only [two_mul, ENat.coe_add] using (add_le_add (hf np) (hf nm))

end PaperI.AffineArea
