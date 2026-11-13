import PaperILean.GoodStripOpenSections
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

namespace PaperI.GoodStrips

open Set FirstOrder Filter MeasureTheory
open scoped Topology ENNReal ContDiff
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private abbrev RD {α : Type} (S : Set (α → ℝ)) :=
  (univ : Set ℝ).Definable Language.ring S

private def regularBase {α ι : Type}
    (G : ι → Set (α ⊕ Fin 3 → ℝ)) (A : Set (α ⊕ Fin 2 → ℝ)) (N : ℕ) :
    Set (α ⊕ Fin 2 → ℝ) :=
  {v | v ∈ A ∧ ∀ (i : ι) (a b : Fin (N+1)),
    v ∈ partialExistsPlane true (mixedJetGraph (G i) a b) ∧
    v ∈ partialExistsPlane false (mixedJetGraph (G i) a b)}

/-- A joint definable family of open sets on which the actual section jets
have all the required section derivatives. -/
def regularPlane {α ι : Type}
    (G : ι → Set (α ⊕ Fin 3 → ℝ)) (A : Set (α ⊕ Fin 2 → ℝ)) (N : ℕ) :
    Set (α ⊕ Fin 2 → ℝ) :=
  planeInterior (regularBase G A N)

theorem regularPlane_definable {α ι : Type} [Finite α] [Fintype ι]
    (G : ι → Set (α ⊕ Fin 3 → ℝ)) {A : Set (α ⊕ Fin 2 → ℝ)}
    (hG : ∀ i, RD (G i)) (hA : RD A) (N : ℕ) : RD (regularPlane G A N) := by
  apply planeInterior_definable
  have hAll : RD {v | ∀ (i : ι) (a b : Fin (N+1)),
      v ∈ partialExistsPlane true (mixedJetGraph (G i) a b) ∧
      v ∈ partialExistsPlane false (mixedJetGraph (G i) a b)} :=
    realDefinable_finite_all fun i => realDefinable_finite_all fun a =>
      realDefinable_finite_all fun b =>
        (partialExistsPlane_definable true (mixedJetGraph_definable (hG i) a b)).inter
          (partialExistsPlane_definable false (mixedJetGraph_definable (hG i) a b))
  exact hA.inter hAll

theorem regularPlane_fiber_open {α ι : Type}
    (G : ι → Set (α ⊕ Fin 3 → ℝ)) (A : Set (α ⊕ Fin 2 → ℝ)) (N : ℕ) (p : α → ℝ) :
    IsOpen (planeFiber (regularPlane G A N) p) := by
  rw [regularPlane, planeInterior_fiber]
  exact isOpen_interior

theorem regularPlane_fiber_subset {α ι : Type}
    (G : ι → Set (α ⊕ Fin 3 → ℝ)) (A : Set (α ⊕ Fin 2 → ℝ)) (N : ℕ) (p : α → ℝ) :
    planeFiber (regularPlane G A N) p ⊆ planeFiber A p := by
  rw [regularPlane, planeInterior_fiber]
  intro x hx
  have hb := interior_subset (s := planeFiber (regularBase G A N) p) hx
  exact hb.1

private theorem regularPlane_fiber_exists {α ι : Type}
    {G : ι → Set (α ⊕ Fin 3 → ℝ)} {A : Set (α ⊕ Fin 2 → ℝ)} {N : ℕ} {p : α → ℝ}
    {x : ℝ × ℝ} (hx : x ∈ planeFiber (regularPlane G A N) p) (i : ι)
    (a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) :
    x ∈ planeFiber (partialExistsPlane true (mixedJetGraph (G i) a b)) p ∧
    x ∈ planeFiber (partialExistsPlane false (mixedJetGraph (G i) a b)) p := by
  rw [regularPlane, planeInterior_fiber] at hx
  exact (interior_subset (s := planeFiber (regularBase G A N) p) hx).2 i
    ⟨a,Nat.lt_succ_of_le ha⟩ ⟨b,Nat.lt_succ_of_le hb⟩

private theorem section_continuous (axis : Bool) (u : ℝ) :
    Continuous (Preparation.sectionPoint axis u) := by
  cases axis
  · exact continuous_const.prodMk continuous_id
  · exact continuous_id.prodMk continuous_const

private theorem section_differentiableAt (axis : Bool) (u t : ℝ) :
    DifferentiableAt ℝ (Preparation.sectionPoint axis u) t := by
  cases axis
  · exact (differentiableAt_const _).prodMk differentiableAt_id
  · exact differentiableAt_id.prodMk (differentiableAt_const _)

private theorem contDiffOn_axis_deriv (axis : Bool) {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (if axis then Preparation.derivX f else Preparation.derivY f) U := by
  let v : ℝ × ℝ := if axis then (1,0) else (0,1)
  have hd := (hf.fderiv_of_isOpen hU (show (↑(⊤ : ℕ∞) : WithTop ℕ∞)+1 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by simp)).clm_apply
    (contDiffOn_const (c := v) (s := U) (n := (∞ : WithTop ℕ∞)))
  apply hd.congr
  intro x hx
  have hfd := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  cases axis
  · change deriv (fun y => f (x.1,y)) x.2 = fderiv ℝ f x v
    have hE : HasDerivAt (fun y : ℝ => (x.1,y)) ((0,1) : ℝ × ℝ) x.2 :=
      (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
    exact (hfd.hasFDerivAt.comp_hasDerivAt x.2 hE).deriv
  · change deriv (fun y => f (y,x.2)) x.1 = fderiv ℝ f x v
    have hE : HasDerivAt (fun y : ℝ => (y,x.2)) ((1,0) : ℝ × ℝ) x.1 :=
      (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
    exact (hfd.hasFDerivAt.comp_hasDerivAt x.1 hE).deriv

private theorem contDiffOn_mixedJet {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a b : ℕ) :
    ContDiffOn ℝ ∞ (Preparation.mixedJet f a b) U := by
  have iter (axis : Bool) (n : ℕ) (g : ℝ × ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g U) :
      ContDiffOn ℝ ∞ ((if axis then Preparation.derivX else Preparation.derivY)^[n] g) U := by
    induction n with
    | zero => exact hg
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      cases axis
      · exact contDiffOn_axis_deriv false hU ih
      · exact contDiffOn_axis_deriv true hU ih
  exact iter false b _ (iter true a f hf)

theorem regularPlane_fiber_null {α ι : Type} [Finite α] [Fintype ι]
    (hNash : PublishedPiecewiseNashExtensions) (hQE : PublishedRealSemialgebraicity)
    (G : ι → Set (α ⊕ Fin 3 → ℝ)) {A : Set (α ⊕ Fin 2 → ℝ)} (N : ℕ)
    (hA : RD A) (p : α → ℝ) (f : ι → ℝ × ℝ → ℝ) {R : Set (ℝ × ℝ)}
    (hR : IsOpen R) (hsub : planeFiber A p ⊆ R)
    (hf : ∀ i, RealizesOn (G i) p (f i) R)
    (hgraph : ∀ i, HasPolynomialSignDescription (scalarGraph (f i) R)) :
    volume (planeFiber A p \ planeFiber (regularPlane G A N) p) = 0 := by
  classical
  choose V hV using fun i => exists_open_full_measure_smooth hNash (f i) R hR (hgraph i)
  let W := interior (planeFiber A p) ∩ ⋂ i, V i
  have hW : IsOpen W := isOpen_interior.inter (isOpen_iInter_of_finite fun i => (hV i).1)
  have hWsub : W ⊆ planeFiber (regularBase G A N) p := by
    intro x hx
    have hxA : x ∈ planeFiber A p := interior_subset (s := planeFiber A p) hx.1
    refine ⟨hxA,?_⟩
    intro i a b
    have hvx : x ∈ V i := mem_iInter.mp hx.2 i
    have hrx : x ∈ R := hsub hxA
    have hcd := contDiffOn_mixedJet (hV i).1 ((hV i).2.2.2.contDiffOn
      (hV i).1.uniqueDiffOn) a b
    have hd := (hcd.contDiffAt ((hV i).1.mem_nhds hvx)).differentiableAt (by simp)
    have hm := mixedJetGraph_realizesOn hR (hf i) a b
    constructor
    · exact (partialExistsPlane_realize hR hm true (u := x.2) (t := x.1) (by simpa
        [Preparation.sectionPoint] using hrx)).mpr (hd.comp x.1 (section_differentiableAt true x.2 x.1))
    · exact (partialExistsPlane_realize hR hm false (u := x.1) (t := x.2) (by simpa
        [Preparation.sectionPoint] using hrx)).mpr (hd.comp x.2 (section_differentiableAt false x.1 x.2))
  have hgood : W ⊆ planeFiber (regularPlane G A N) p := by
    rw [regularPlane, planeInterior_fiber]
    exact interior_maximal hWsub hW
  let bad := (planeFiber A p \ interior (planeFiber A p)) ∪ ⋃ i, R \ V i
  apply measure_mono_null (t := bad) _ _
  · intro x hx
    by_cases hi : x ∈ interior (planeFiber A p)
    · right
      by_contra! hn
      apply hx.2 (hgood ⟨hi,?_⟩)
      apply mem_iInter.mpr
      intro i
      by_contra hi
      exact hn (mem_iUnion.mpr ⟨i,hsub hx.1,hi⟩)
    · exact Or.inl ⟨hx.1,hi⟩
  · exact measure_union_null (volume_diff_interior_eq_zero _ (planeFiber_sign hQE hA p))
      (measure_iUnion_null fun i => (hV i).2.2.1)

private theorem horizontalJet_eq_iteratedDeriv (f : ℝ × ℝ → ℝ) (n : ℕ)
    (x y : ℝ) :
    Preparation.horizontalJet f n (x,y) = iteratedDeriv n (fun x => f (x,y)) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [Preparation.horizontalJet, Function.iterate_succ_apply', Preparation.derivX,
      iteratedDeriv_succ]
    rw [show (fun z => Preparation.derivX^[n] f (z,y)) =
      iteratedDeriv n (fun z => f (z,y)) from funext ih]

theorem regularPlane_horizontal_smooth {α ι : Type}
    (G : ι → Set (α ⊕ Fin 3 → ℝ)) (A : Set (α ⊕ Fin 2 → ℝ)) (N : ℕ)
    (p : α → ℝ) (f : ι → ℝ × ℝ → ℝ) {R : Set (ℝ × ℝ)}
    (hR : IsOpen R) (hsub : planeFiber A p ⊆ R)
    (hf : ∀ i, RealizesOn (G i) p (f i) R) (i : ι) (y : ℝ) :
    ContDiffOn ℝ (N : ℕ) (fun x => f i (x,y))
      ((fun x => (x,y)) ⁻¹' planeFiber (regularPlane G A N) p) := by
  apply contDiffOn_of_iteratedDifferentiable N
  · exact (regularPlane_fiber_open G A N p).preimage (section_continuous true y)
  · intro n hn x hx
    have hr : (x,y) ∈ R := hsub (regularPlane_fiber_subset G A N p hx)
    have hreg := (regularPlane_fiber_exists hx i n 0 hn (Nat.zero_le _)).1
    have hm := mixedJetGraph_realizesOn hR (hf i) n 0
    have hd := (partialExistsPlane_realize hR hm true (u := y) (t := x) hr).mp hreg
    apply DifferentiableAt.differentiableWithinAt
    convert hd using 1
    funext z
    exact (horizontalJet_eq_iteratedDeriv (f i) n z y).symm

theorem regularPlane_vertical_smooth {α ι : Type}
    (G : ι → Set (α ⊕ Fin 3 → ℝ)) (A : Set (α ⊕ Fin 2 → ℝ)) (N : ℕ)
    (p : α → ℝ) (f : ι → ℝ × ℝ → ℝ) {R : Set (ℝ × ℝ)}
    (hR : IsOpen R) (hsub : planeFiber A p ⊆ R)
    (hf : ∀ i, RealizesOn (G i) p (f i) R) (i : ι) (a : ℕ) (ha : a ≤ N) (x : ℝ) :
    ContDiffOn ℝ ((N-a : ℕ) : WithTop ℕ∞) (fun y => Preparation.horizontalJet (f i) a (x,y))
      (Prod.mk x ⁻¹' planeFiber (regularPlane G A N) p) := by
  apply contDiffOn_of_iteratedDifferentiable (N-a)
  · exact (regularPlane_fiber_open G A N p).preimage (section_continuous false x)
  · intro n hn y hy
    have hr : (x,y) ∈ R := hsub (regularPlane_fiber_subset G A N p hy)
    have hreg := (regularPlane_fiber_exists hy i a n ha (hn.trans (Nat.sub_le _ _))).2
    have hm := mixedJetGraph_realizesOn hR (hf i) a n
    have hd := (partialExistsPlane_realize hR hm false (u := x) (t := y) hr).mp hreg
    apply DifferentiableAt.differentiableWithinAt
    convert hd using 1
    funext z
    exact (Preparation.mixedJet_eq_iteratedDeriv (f i) a n (x,z)).symm

end PaperI.GoodStrips
