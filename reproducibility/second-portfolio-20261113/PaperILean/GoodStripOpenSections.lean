import PaperILean.GoodStripJetGraphs
import PaperILean.GoodStripRegularLocus

noncomputable section

namespace PaperI.GoodStrips

open Set FirstOrder Filter MeasureTheory
open scoped Topology ENNReal ContDiff

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private abbrev RD {α : Type} (S : Set (α → ℝ)) :=
  (univ : Set ℝ).Definable Language.ring S

def planeFiber {α : Type} (A : Set (α ⊕ Fin 2 → ℝ)) (p : α → ℝ) : Set (ℝ × ℝ) :=
  {x | Sum.elim p ![x.1,x.2] ∈ A}

theorem planeFiber_sign {α : Type} [Finite α] (hQE : PublishedRealSemialgebraicity)
    {A : Set (α ⊕ Fin 2 → ℝ)} (hA : RD A) (p : α → ℝ) :
    HasPolynomialSignDescription {v : Fin 2 → ℝ | (v 0,v 1) ∈ planeFiber A p} := by
  obtain ⟨F,hF⟩ := hQE.finite_sign_description A hA
  have hp := polynomialSignDetermined_projectionFiber p F A hF
  have he : {v : Fin 2 → ℝ | (v 0,v 1) ∈ planeFiber A p} = projectionFiber A p := by
    ext v
    have hv : ![v 0,v 1] = v := by funext i; fin_cases i <;> rfl
    simp [planeFiber,projectionFiber,hv]
  rw [he]
  exact ⟨_,hp⟩

theorem planeFiber_measurable {α : Type} [Finite α] (hQE : PublishedRealSemialgebraicity)
    {A : Set (α ⊕ Fin 2 → ℝ)} (hA : RD A) (p : α → ℝ) :
    MeasurableSet (planeFiber A p) := by
  have h := hasPolynomialSignDescription_borel (planeFiber_sign hQE hA p)
  have hc : Continuous (fun x : ℝ × ℝ => (![x.1,x.2] : Fin 2 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  have h' : MeasurableSet {v : Fin 2 → ℝ | (v 0,v 1) ∈ planeFiber A p} := by
    exact (BorelSpace.measurable_eq (α := Fin 2 → ℝ)).symm ▸ h
  exact hc.measurable h'

def sectionFamily {α : Type} (axis : Bool) (A : Set (α ⊕ Fin 2 → ℝ)) :
    Set ((α ⊕ Unit) ⊕ Unit → ℝ) :=
  {v | let u := v (Sum.inl (Sum.inr ()))
       let t := v (Sum.inr ())
       let x := Preparation.sectionPoint axis u t
       Sum.elim (fun i => v (Sum.inl (Sum.inl i))) ![x.1,x.2] ∈ A}

theorem sectionFamily_definable {α : Type} [Finite α] (axis : Bool)
    {A : Set (α ⊕ Fin 2 → ℝ)} (hA : RD A) : RD (sectionFamily axis A) := by
  let e : α ⊕ Fin 2 → (α ⊕ Unit) ⊕ Unit :=
    Sum.elim (Sum.inl ∘ Sum.inl) ![
      if axis then Sum.inr () else Sum.inl (Sum.inr ()),
      if axis then Sum.inl (Sum.inr ()) else Sum.inr ()]
  convert hA.preimage_comp e using 1
  ext v
  have he : v ∘ e = Sum.elim (fun i => v (Sum.inl (Sum.inl i))) ![
      (Preparation.sectionPoint axis (v (Sum.inl (Sum.inr ()))) (v (Sum.inr ()))).1,
      (Preparation.sectionPoint axis (v (Sum.inl (Sum.inr ()))) (v (Sum.inr ()))).2] := by
    funext i
    rcases i with i | i
    · rfl
    · fin_cases i <;> cases axis <;> rfl
  simp only [sectionFamily,mem_preimage,mem_setOf_eq,he]

theorem sectionFamily_fiber {α : Type} (axis : Bool) (A : Set (α ⊕ Fin 2 → ℝ))
    (p : α → ℝ) (u : ℝ) :
    scalarProjectionFiber (sectionFamily axis A) (Sum.elim p (fun _ : Unit => u)) =
      Preparation.sectionPoint axis u ⁻¹' planeFiber A p := by
  ext t
  simp [scalarProjectionFiber,projectionFiber,sectionFamily,planeFiber,Function.comp_def]

def planeInterior {α : Type} (A : Set (α ⊕ Fin 2 → ℝ)) :
    Set (α ⊕ Fin 2 → ℝ) :=
  {v | (v (Sum.inr 0),v (Sum.inr 1)) ∈ interior (planeFiber A (v ∘ Sum.inl))}

theorem planeInterior_fiber {α : Type} (A : Set (α ⊕ Fin 2 → ℝ)) (p : α → ℝ) :
    planeFiber (planeInterior A) p = interior (planeFiber A p) := by
  ext x
  simp [planeFiber,planeInterior]

theorem planeInterior_definable {α : Type} [Finite α]
    {A : Set (α ⊕ Fin 2 → ℝ)} (hA : RD A) : RD (planeInterior A) := by
  let β := α ⊕ Fin 2
  let γ := β ⊕ Unit
  let η := γ ⊕ Fin 2
  let X : η → MvPolynomial η ℝ := MvPolynomial.X
  let e : β → η := Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr
  let u : Fin 2 → η := Sum.inl ∘ Sum.inl ∘ Sum.inr
  let r : η := Sum.inl (Sum.inr ())
  let near (j : Fin 2) : Set (η → ℝ) :=
    {v | v (u j)-v r < v (Sum.inr j) ∧ v (Sum.inr j) < v (u j)+v r}
  have hnear (j : Fin 2) : RD (near j) := by
    simpa [near,X,map_add,map_sub] using
      (realPolynomial_lt_definable (X (u j)-X r) (X (Sum.inr j))).inter
      (realPolynomial_lt_definable (X (Sum.inr j)) (X (u j)+X r))
  have hall := realDefinable_forall
    ((((hnear 0).inter (hnear 1)).compl).union (hA.preimage_comp e))
  have hr := realPolynomial_lt_definable (0 : MvPolynomial γ ℝ) (MvPolynomial.X (Sum.inr ()))
  convert realDefinable_exists (hr.inter hall) using 1
  ext v
  change (v (Sum.inr 0),v (Sum.inr 1)) ∈ interior (planeFiber A (v ∘ Sum.inl)) ↔ _
  symm
  rw [mem_interior_iff_mem_nhds,Metric.mem_nhds_iff]
  simp only [mem_setOf_eq, mem_inter_iff, map_zero, MvPolynomial.eval_X, Sum.elim_inr,
    mem_union,mem_compl_iff,mem_preimage,near,u,r,Function.comp_apply,Sum.elim_inl]
  have hvec (q : Fin 2 → ℝ) : ![q 0,q 1] = q := by funext i; fin_cases i <;> rfl
  have hmem (w : Unit → ℝ) (q : Fin 2 → ℝ) :
      Sum.elim (Sum.elim v w) q ∘ e ∈ A ↔ (q 0,q 1) ∈ planeFiber A (v ∘ Sum.inl) := by
    have he : Sum.elim (Sum.elim v w) q ∘ e = Sum.elim (v ∘ Sum.inl) q := by
      funext i
      rcases i with i | i <;> rfl
    rw [he]
    simp only [planeFiber,mem_setOf_eq,hvec]
  constructor
  · rintro ⟨w,hw,h⟩
    refine ⟨w (),hw,?_⟩
    intro p hp
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hp
    obtain ⟨hx,hy⟩ := hp
    have hx' := abs_lt.mp hx
    have hy' := abs_lt.mp hy
    rcases h ![p.1,p.2] with hbad | hok
    · exact False.elim (hbad ⟨⟨by dsimp; linarith [hx'.1], by dsimp; linarith [hx'.2]⟩,
        ⟨by dsimp; linarith [hy'.1],by dsimp; linarith [hy'.2]⟩⟩)
    · exact (hmem w ![p.1,p.2]).mp hok
  · rintro ⟨w,hw,h⟩
    refine ⟨fun _ => w,hw,?_⟩
    intro q
    by_cases hbad : (v (Sum.inr 0)-w < q 0 ∧ q 0 < v (Sum.inr 0)+w) ∧
        (v (Sum.inr 1)-w < q 1 ∧ q 1 < v (Sum.inr 1)+w)
    · apply Or.inr
      apply (hmem (fun _ => w) q).mpr
      apply h
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      exact ⟨abs_lt.mpr ⟨by linarith [hbad.1.1],by linarith [hbad.1.2]⟩,
        abs_lt.mpr ⟨by linarith [hbad.2.1],by linarith [hbad.2.2]⟩⟩
    · exact Or.inl hbad

def partialExistsPlane {α : Type} (axis : Bool) (G : Set (α ⊕ Fin 3 → ℝ)) :
    Set (α ⊕ Fin 2 → ℝ) :=
  {v | let x := v (Sum.inr 0)
       let y := v (Sum.inr 1)
       Sum.elim (Sum.elim (v ∘ Sum.inl) (fun _ : Unit => if axis then y else x))
         (fun _ : Unit => if axis then x else y) ∈
         graphDerivativeExistsRelation (sectionGraph axis G)}

theorem partialExistsPlane_definable {α : Type} [Finite α] (axis : Bool)
    {G : Set (α ⊕ Fin 3 → ℝ)} (hG : RD G) : RD (partialExistsPlane axis G) := by
  let e : (α ⊕ Unit) ⊕ Unit → α ⊕ Fin 2 :=
    Sum.elim (Sum.elim Sum.inl (fun _ => Sum.inr (if axis then 1 else 0)))
      (fun _ => Sum.inr (if axis then 0 else 1))
  have h := (graphDerivativeExistsRelation_definable (sectionGraph_definable axis hG)).preimage_comp e
  convert h using 1
  ext v
  have he : v ∘ e = Sum.elim (Sum.elim (v ∘ Sum.inl)
      (fun _ : Unit => if axis then v (Sum.inr 1) else v (Sum.inr 0)))
      (fun _ : Unit => if axis then v (Sum.inr 0) else v (Sum.inr 1)) := by
    funext i
    rcases i with (i|i)|i
    · rfl
    · cases axis <;> rfl
    · cases axis <;> rfl
  simp only [partialExistsPlane,mem_setOf_eq,mem_preimage,he]

theorem partialExistsPlane_realize {α : Type} {G : Set (α ⊕ Fin 3 → ℝ)}
    {p : α → ℝ} {f : ℝ × ℝ → ℝ} {R : Set (ℝ × ℝ)} (hR : IsOpen R)
    (hG : RealizesOn G p f R) (axis : Bool) {u t : ℝ}
    (ht : Preparation.sectionPoint axis u t ∈ R) :
    Preparation.sectionPoint axis u t ∈ planeFiber (partialExistsPlane axis G) p ↔
      DifferentiableAt ℝ (fun s => f (Preparation.sectionPoint axis u s)) t := by
  have hc : Continuous (Preparation.sectionPoint axis u) := by
    cases axis
    · change Continuous (fun s : ℝ => (u,s))
      exact continuous_const.prodMk continuous_id
    · change Continuous (fun s : ℝ => (s,u))
      exact continuous_id.prodMk continuous_const
  let pp := Sum.elim p (fun _ : Unit => u)
  have hloc : ∀ᶠ s in 𝓝 t, ∀ y, Sum.elim pp ![s,y] ∈ sectionGraph axis G ↔
      y = f (Preparation.sectionPoint axis u s) := by
    have hn : ∀ᶠ s in 𝓝 t, Preparation.sectionPoint axis u s ∈ R :=
      hc.continuousAt (hR.mem_nhds ht)
    filter_upwards [hn] with s hs y
    exact (sectionGraph_realize axis G p u s y).trans (hG _ hs y)
  have he : Sum.elim pp (fun _ : Unit => t) ∈
      graphDerivativeExistsRelation (sectionGraph axis G) ↔
      DifferentiableAt ℝ (fun s => f (Preparation.sectionPoint axis u s)) t := by
    change (∃ w : Unit → ℝ,
      Sum.elim ((Sum.elim pp (fun _ : Unit => t)) ∘ Sum.inl)
        ![(Sum.elim pp (fun _ : Unit => t)) (Sum.inr ()),w ()] ∈
        graphDerivativeRelation (sectionGraph axis G) ∧ w () ∈ univ) ↔ _
    simp only [Sum.elim_comp_inl, Sum.elim_inr, mem_univ, and_true]
    constructor
    · rintro ⟨w,hw⟩
      exact ((graphDerivativeRelation_realize_iff_of_local_graph _ _ _ _ _ hloc).mp hw).differentiableAt
    · intro hf
      exact ⟨fun _ => deriv (fun s => f (Preparation.sectionPoint axis u s)) t,
        (graphDerivativeRelation_realize_iff_of_local_graph _ _ _ _ _ hloc).mpr hf.hasDerivAt⟩
  convert he using 1
  cases axis <;> simp [pp,planeFiber,partialExistsPlane,Preparation.sectionPoint]

theorem contDiffOn_of_iteratedDifferentiable (N : ℕ) (f : ℝ → ℝ) {U : Set ℝ}
    (hU : IsOpen U)
    (hd : ∀ n ≤ N, DifferentiableOn ℝ (iteratedDeriv n f) U) :
    ContDiffOn ℝ (N : ℕ) f U := by
  induction N generalizing f with
  | zero => simpa only [Nat.cast_zero,contDiffOn_zero] using
      (hd 0 le_rfl).continuousOn
  | succ N ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hU]
    refine ⟨?_,?_,ih (deriv f) ?_⟩
    · simpa only [iteratedDeriv_zero] using hd 0 (Nat.zero_le _)
    · simp
    · intro n hn
      rw [← iteratedDeriv_succ']
      exact hd (n+1) (by omega)

end PaperI.GoodStrips
