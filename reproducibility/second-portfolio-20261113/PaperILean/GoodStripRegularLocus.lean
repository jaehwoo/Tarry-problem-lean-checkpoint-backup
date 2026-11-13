import PaperILean.PublishedUniformAnalyticCuts
import PaperILean.PolynomialSignNeighborhood
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.MvPolynomial.Polynomial

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PaperI.GoodStrips

private theorem finPolynomial_zero_volume (n : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p ≠ 0) : volume {v | MvPolynomial.eval v p = 0} = 0 := by
  induction n with
  | zero =>
    have hconst : (MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)) p ≠ 0 := by
      intro h
      apply hp
      exact (MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).injective (h.trans (map_zero _).symm)
    have he (v : Fin 0 → ℝ) :
        MvPolynomial.eval v p = (MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)) p := by
      rw [MvPolynomial.isEmptyAlgEquiv_apply, MvPolynomial.aeval_def]
      change MvPolynomial.eval v p = MvPolynomial.eval₂ (RingHom.id ℝ) (fun i => isEmptyElim i) p
      rw [MvPolynomial.eval₂_id, Subsingleton.elim v (fun i => isEmptyElim i)]
    have hz : {v | MvPolynomial.eval v p = 0} = ∅ := by
      ext v
      simp only [mem_setOf_eq, mem_empty_iff_false]
      exact ⟨fun hv => hconst ((he v).symm.trans hv), False.elim⟩
    rw [hz, measure_empty]
  | succ n ih =>
    let Q := MvPolynomial.finSuccEquiv ℝ n p
    have hQ : Q ≠ 0 := by
      intro h
      apply hp
      exact (MvPolynomial.finSuccEquiv ℝ n).injective (h.trans (map_zero _).symm)
    obtain ⟨j, hj⟩ : ∃ j, Q.coeff j ≠ 0 := by
      by_contra! hz
      exact hQ (Polynomial.ext (fun j => by simp [hz j]))
    let Z : Set (ℝ × (Fin n → ℝ)) := {a | MvPolynomial.eval (Fin.cons a.1 a.2) p = 0}
    have hZ : MeasurableSet Z := by
      apply IsClosed.measurableSet
      apply isClosed_eq _ continuous_const
      apply (MvPolynomial.continuous_eval p).comp
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using continuous_fst
      · simpa only [Fin.cons_succ] using (continuous_apply j).comp continuous_snd
    have ha : ∀ᵐ v : Fin n → ℝ ∂volume, MvPolynomial.eval v (Q.coeff j) ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not] using ih (Q.coeff j) hj
    have hfiber : (fun v : Fin n → ℝ => volume ((fun x : ℝ => (x,v)) ⁻¹' Z)) =ᶠ[ae volume]
        (fun _ => 0) := by
      filter_upwards [ha] with v hv
      let q := Q.map (MvPolynomial.eval v)
      have hq : q ≠ 0 := by
        intro h
        have hc := congrArg (fun w : Polynomial ℝ => w.coeff j) h
        exact hv (by simpa [q, Polynomial.coeff_map] using hc)
      have he : (fun x : ℝ => (x,v)) ⁻¹' Z = {x | q.IsRoot x} := by
        ext x
        simp only [preimage, Z, mem_setOf_eq, Polynomial.IsRoot]
        rw [MvPolynomial.eval_eq_eval_mv_eval']
      rw [he]
      exact (Polynomial.finite_setOf_isRoot hq).measure_zero volume
    have hz : (volume : Measure (ℝ × (Fin n → ℝ))) Z = 0 := by
      change (volume.prod volume) Z = 0
      rw [Measure.prod_apply_symm hZ, lintegral_congr_ae hfiber, lintegral_zero]
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    have he : MeasurePreserving e volume volume :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℝ)) 0
    have hpull : e ⁻¹' Z = {v | MvPolynomial.eval v p = 0} := by
      ext v
      have hv : Fin.cons (e v).1 (e v).2 = v := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl
      simp only [preimage, Z, mem_setOf_eq, hv]
    rw [← hpull, he.measure_preimage hZ.nullMeasurableSet, hz]

private def pairOf : (Fin 2 → ℝ) → ℝ × ℝ := fun v => (v 0, v 1)

private def vecOf : ℝ × ℝ → Fin 2 → ℝ := fun x => ![x.1,x.2]

private theorem pairOf_vecOf (x : ℝ × ℝ) : pairOf (vecOf x) = x := by
  cases x
  rfl

private theorem vecOf_pairOf (x : Fin 2 → ℝ) : vecOf (pairOf x) = x := by
  funext i
  fin_cases i <;> rfl

private theorem continuous_pairOf : Continuous pairOf :=
  (continuous_apply 0).prodMk (continuous_apply 1)

private noncomputable def vecLinear : (ℝ × ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi (fun i => Fin.cases (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (fun _ => ContinuousLinearMap.snd ℝ ℝ ℝ) i)

private theorem vecLinear_apply (x : ℝ × ℝ) : vecLinear x = vecOf x := by
  funext i
  fin_cases i <;> rfl

private theorem continuous_vecOf : Continuous vecOf := by
  rw [← show ⇑vecLinear = vecOf from funext vecLinear_apply]
  exact vecLinear.continuous

private theorem measurePreserving_vecOf : MeasurePreserving vecOf volume volume := by
  let e₀ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0
  let e₁ := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  let e := e₀.trans ((MeasurableEquiv.refl ℝ).prodCongr e₁)
  have h₀ : MeasurePreserving e₀ volume volume :=
    measurePreserving_piFinSuccAbove (fun _ : Fin 2 => (volume : Measure ℝ)) 0
  have h₁ : MeasurePreserving e₁ volume volume :=
    measurePreserving_piUnique (fun _ : Fin 1 => (volume : Measure ℝ))
  have he : MeasurePreserving e volume volume := ((MeasurePreserving.id _).prod h₁).comp h₀
  have hf : ⇑e = pairOf := by
    funext v
    rfl
  have hv : ⇑e.symm = vecOf := by
    funext x
    apply e.injective
    rw [e.apply_symm_apply, hf, pairOf_vecOf]
  rw [← hv]
  exact he.symm e

private theorem polynomial_sign_eventually {E : Type*} [TopologicalSpace E]
    {e : E → ℝ} (he : Continuous e) {x : E} (hx : e x ≠ 0) :
    ∀ᶠ y in 𝓝 x, RealSignEquivalent (e x) (e y) := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · filter_upwards [(isOpen_lt he continuous_const).eventually_mem hneg] with y hy
    change e y < 0 at hy
    exact ⟨iff_of_false hx (ne_of_lt hy), iff_of_false (not_lt_of_gt hneg) (not_lt_of_gt hy)⟩
  · filter_upwards [(isOpen_lt continuous_const he).eventually_mem hpos] with y hy
    change 0 < e y at hy
    exact ⟨iff_of_false hx (ne_of_gt hy), iff_of_true hpos hy⟩

private theorem volume_diff_interior_of_eval_null {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [MeasureSpace E] {ι : Type*}
    (e : E → ι → ℝ) (he : Continuous e) (A : Set E)
    (hA : HasPolynomialSignDescription {v | ∃ x ∈ A, e x = v})
    (hInj : Function.Injective e)
    (hnull : ∀ p : MvPolynomial ι ℝ, p ≠ 0 → volume {x | MvPolynomial.eval (e x) p = 0} = 0) :
    volume (A \ interior A) = 0 := by
  classical
  obtain ⟨S, hS⟩ := hA
  let bad (p : MvPolynomial ι ℝ) : Set E :=
    if p = 0 then ∅ else {x | MvPolynomial.eval (e x) p = 0}
  have hbad (p : MvPolynomial ι ℝ) : volume (bad p) = 0 := by
    by_cases hp : p = 0
    · simp [bad, hp]
    · simpa [bad, hp] using hnull p hp
  apply measure_mono_null (t := ⋃ p ∈ S, bad p) _ _
  · intro x hx
    by_contra hnot
    have hev : ∀ᶠ y in 𝓝 x, ∀ p ∈ S,
        RealSignEquivalent (MvPolynomial.eval (e x) p) (MvPolynomial.eval (e y) p) := by
      rw [Finset.eventually_all]
      intro p hp
      by_cases hp₀ : p = 0
      · simp [hp₀, RealSignEquivalent]
      · apply polynomial_sign_eventually ((MvPolynomial.continuous_eval p).comp he)
        intro hz
        change MvPolynomial.eval (e x) p = 0 at hz
        exact hnot (mem_iUnion.2 ⟨p, mem_iUnion.2 ⟨hp, by simp [bad, hp₀, hz]⟩⟩)
    apply hx.2
    rw [mem_interior_iff_mem_nhds]
    filter_upwards [hev] with y hy
    obtain ⟨z, hz, hzy⟩ := (hS (e x) (e y) hy).mp ⟨x,hx.1,rfl⟩
    exact (hInj hzy) ▸ hz
  · exact le_antisymm ((measure_biUnion_finset_le S bad).trans_eq
      (Finset.sum_eq_zero (fun p _ => hbad p))) bot_le

theorem volume_diff_interior_eq_zero (A : Set (ℝ × ℝ))
    (hA : HasPolynomialSignDescription {v : Fin 2 → ℝ | (v 0,v 1) ∈ A}) :
    volume (A \ interior A) = 0 := by
  have hset : {v | ∃ x ∈ A, vecOf x = v} = {v : Fin 2 → ℝ | (v 0,v 1) ∈ A} := by
    ext v
    change (∃ x ∈ A, vecOf x = v) ↔ pairOf v ∈ A
    exact ⟨fun ⟨x,hx,h⟩ => by simpa only [← h, pairOf_vecOf] using hx,
      fun h => ⟨pairOf v,h,vecOf_pairOf v⟩⟩
  apply volume_diff_interior_of_eval_null vecOf continuous_vecOf A (hset ▸ hA)
    (Function.LeftInverse.injective pairOf_vecOf)
  intro p hp
  let Z := {v | MvPolynomial.eval v p = 0}
  exact (measurePreserving_vecOf.measure_preimage
    ((isClosed_eq (MvPolynomial.continuous_eval p) continuous_const).measurableSet.nullMeasurableSet :
      NullMeasurableSet Z volume)).trans (finPolynomial_zero_volume 2 p hp)

theorem volume_diff_interior_real_eq_zero (A : Set ℝ)
    (hA : HasPolynomialSignDescription {v : Unit → ℝ | v () ∈ A}) :
    volume (A \ interior A) = 0 := by
  let e : ℝ → Unit → ℝ := fun x _ => x
  have he : Continuous e := continuous_pi (fun _ => continuous_id)
  have hinj : Function.Injective e := fun _ _ h => congrFun h ()
  have heA : {v | ∃ x ∈ A, e x = v} = {v : Unit → ℝ | v () ∈ A} := by
    ext v
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hv
      exact ⟨v (),hv,funext (fun i => by cases i; rfl)⟩
  apply volume_diff_interior_of_eval_null e he A (heA ▸ hA) hinj
  intro p hp
  let s : Unit ≃ Fin 1 := Equiv.ofUnique _ _
  let q := MvPolynomial.renameEquiv ℝ s p
  have hq : q ≠ 0 := by
    intro h
    apply hp
    exact (MvPolynomial.renameEquiv ℝ s).injective (h.trans (map_zero _).symm)
  let Z : Set (Fin 1 → ℝ) := {v | MvPolynomial.eval v q = 0}
  let t := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have ht : MeasurePreserving t volume volume :=
    measurePreserving_piUnique (fun _ : Fin 1 => (volume : Measure ℝ))
  have hZ : MeasurableSet Z :=
    (isClosed_eq (MvPolynomial.continuous_eval q) continuous_const).measurableSet
  have heq : t.symm ⁻¹' Z = {x | MvPolynomial.eval (e x) p = 0} := by
    ext x
    have hconst : (t.symm x) ∘ s = e x := by
      funext i
      change t.symm x (s i) = x
      rw [Subsingleton.elim (s i) default]
      exact t.apply_symm_apply x
    simp only [preimage, Z, mem_setOf_eq, q, MvPolynomial.renameEquiv_apply,
      MvPolynomial.eval_rename, hconst]
  rw [← heq, (ht.symm t).measure_preimage hZ.nullMeasurableSet]
  exact finPolynomial_zero_volume 1 q hq

/-- The actual scalar graph in the physical pair coordinates. -/
def scalarGraph (f : ℝ × ℝ → ℝ) (R : Set (ℝ × ℝ)) : Set (Fin 3 → ℝ) :=
  {v | (v 0,v 1) ∈ R ∧ v 2 = f (v 0,v 1)}

/-- Interior pieces of the finite Nash decomposition exhaust the open
domain up to a null set, even when the original scalar jumps on lower
dimensional strata. -/
theorem exists_open_full_measure_smooth (hNash : PublishedPiecewiseNashExtensions)
    (f : ℝ × ℝ → ℝ) (R : Set (ℝ × ℝ)) (_hR : IsOpen R)
    (hgraph : HasPolynomialSignDescription (scalarGraph f R)) :
    ∃ U, IsOpen U ∧ U ⊆ R ∧ volume (R \ U) = 0 ∧ AnalyticOnNhd ℝ f U := by
  classical
  let F := f ∘ pairOf
  let S : Set (Fin 2 → ℝ) := pairOf ⁻¹' R
  let e : Fin 2 ⊕ Unit ≃ Fin 3 :=
    (Equiv.sumCongr (Equiv.refl (Fin 2)) (Fintype.equivFin Unit)).trans finSumFinEquiv
  have hgraph' : HasPolynomialSignDescription {v | v ∘ Sum.inl ∈ S ∧ v (Sum.inr ()) = F (v ∘ Sum.inl)} := by
    obtain ⟨L,hL⟩ := hgraph
    refine ⟨L.image (MvPolynomial.rename e.symm), ?_⟩
    intro v w h
    have hs : ∀ p ∈ L, RealSignEquivalent
        (MvPolynomial.eval (v ∘ e.symm) p) (MvPolynomial.eval (w ∘ e.symm) p) := by
      intro p hp
      have ht := h (MvPolynomial.rename e.symm p) (Finset.mem_image_of_mem _ hp)
      simpa only [MvPolynomial.eval_rename] using ht
    have he₀ : e.symm 0 = Sum.inl 0 := by apply e.injective; rw [e.apply_symm_apply]; rfl
    have he₁ : e.symm 1 = Sum.inl 1 := by apply e.injective; rw [e.apply_symm_apply]; rfl
    have he₂ : e.symm 2 = Sum.inr () := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Fin.ext
      change 2 = 2 + ((Fintype.equivFin Unit) ()).val
      have h := ((Fintype.equivFin Unit) ()).isLt
      norm_num at h ⊢
    simpa only [scalarGraph, S, F, mem_setOf_eq, mem_preimage, Function.comp_apply, pairOf,
      he₀,he₁,he₂] using hL (v ∘ e.symm) (w ∘ e.symm) hs
  obtain ⟨n,V,hV,hcover⟩ := hNash.finite_analytic_pieces (Fin 2) F S hgraph'
  let W (i : Fin n) := vecOf ⁻¹' V i
  let U := ⋃ i, interior (W i)
  have hW i : W i ⊆ R := by
    intro x hx
    have hx' := (hV i).2.1 hx
    simpa only [S, mem_preimage, pairOf_vecOf] using hx'
  have hRcover (x : ℝ × ℝ) (hx : x ∈ R) : ∃ i, x ∈ W i :=
    hcover (vecOf x) (by simpa only [S, mem_preimage, pairOf_vecOf] using hx)
  refine ⟨U, isOpen_iUnion (fun _ => isOpen_interior), ?_, ?_, ?_⟩
  · exact iUnion_subset (fun i => interior_subset.trans (hW i))
  · apply measure_mono_null (t := ⋃ i, W i \ interior (W i)) _ _
    · intro x hx
      obtain ⟨i, hi⟩ := hRcover x hx.1
      exact mem_iUnion.2 ⟨i,hi,fun hxi => hx.2 (mem_iUnion.2 ⟨i,hxi⟩)⟩
    · apply measure_iUnion_null
      intro i
      apply volume_diff_interior_eq_zero
      have heq : {v : Fin 2 → ℝ | pairOf v ∈ W i} = V i := by
        ext v
        change vecOf (pairOf v) ∈ V i ↔ v ∈ V i
        rw [vecOf_pairOf]
      change HasPolynomialSignDescription {v : Fin 2 → ℝ | pairOf v ∈ W i}
      rw [heq]
      exact (hV i).1
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    have hm : vecOf x ∈ V i := interior_subset (s := W i) hi
    obtain ⟨g,hg,hgeq⟩ := (hV i).2.2 (vecOf x) hm
    have hAnal : AnalyticAt ℝ (g ∘ vecOf) x := by
      have hv : AnalyticAt ℝ vecOf x := by
        rw [← show ⇑vecLinear = vecOf from funext vecLinear_apply]
        exact vecLinear.analyticAt x
      exact hg.comp hv
    apply hAnal.congr
    have ht : Tendsto vecOf (𝓝 x) (𝓝 (vecOf x)) := continuous_vecOf.continuousAt
    have hnear : ∀ᶠ y in 𝓝 x, vecOf y ∈ V i :=
      (isOpen_interior.eventually_mem hi).mono (fun _ hy => interior_subset (s := W i) hy)
    filter_upwards [ht.eventually hgeq, hnear] with y hy hy'
    simpa only [Function.comp_apply, F, pairOf_vecOf] using hy hy'

end PaperI.GoodStrips
