import PaperILean.PreparationFormat
import PaperILean.GraphDerivativeLoci

noncomputable section

namespace PaperI.GoodStrips

open Set FirstOrder Filter
open scoped Topology

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private abbrev RD {α : Type} (S : Set (α → ℝ)) :=
  (univ : Set ℝ).Definable Language.ring S

/-- The first-order graph of Lean's actual total derivative. Derivative
existence on the final open analytic locus is proved separately. -/
def totalDerivativeGraph {α : Type} (G : Set (α ⊕ Fin 2 → ℝ)) :
    Set (α ⊕ Fin 2 → ℝ) :=
  graphDerivativeRelation G ∪
    {v | Sum.elim (v ∘ Sum.inl) (fun _ : Unit => v (Sum.inr 0)) ∉
        graphDerivativeExistsRelation G ∧ v (Sum.inr 1) = 0}

theorem totalDerivativeGraph_definable {α : Type} [Finite α]
    {G : Set (α ⊕ Fin 2 → ℝ)} (hG : RD G) : RD (totalDerivativeGraph G) := by
  let e : α ⊕ Unit → α ⊕ Fin 2 := Sum.elim Sum.inl (fun _ => Sum.inr 0)
  have hn := ((graphDerivativeExistsRelation_definable hG).preimage_comp e).compl
  have hz := realPolynomial_zero_definable (MvPolynomial.X (Sum.inr 1 : α ⊕ Fin 2))
  convert (graphDerivativeRelation_definable hG).union (hn.inter hz) using 1
  ext v
  have he : v ∘ e = Sum.elim (v ∘ Sum.inl) (fun _ : Unit => v (Sum.inr 0)) := by
    funext i
    cases i <;> rfl
  simp only [totalDerivativeGraph, mem_union, mem_setOf_eq, mem_inter_iff,
    mem_compl_iff, mem_preimage, he, MvPolynomial.eval_X]

theorem totalDerivativeGraph_realize {α : Type}
    (G : Set (α ⊕ Fin 2 → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (t d : ℝ)
    (hG : ∀ᶠ s in 𝓝 t, ∀ y, Sum.elim p ![s,y] ∈ G ↔ y = f s) :
    Sum.elim p ![t,d] ∈ totalDerivativeGraph G ↔ d = deriv f t := by
  have he : Sum.elim p (fun _ : Unit => t) ∈ graphDerivativeExistsRelation G ↔
      DifferentiableAt ℝ f t := by
    change (∃ w : Unit → ℝ,
      Sum.elim ((Sum.elim p (fun _ : Unit => t)) ∘ Sum.inl)
        ![(Sum.elim p (fun _ : Unit => t)) (Sum.inr ()),w ()] ∈ graphDerivativeRelation G ∧ w () ∈ univ) ↔ _
    simp only [Sum.elim_comp_inl, Sum.elim_inr, mem_univ, and_true]
    constructor
    · rintro ⟨w,hw⟩
      exact ((graphDerivativeRelation_realize_iff_of_local_graph G p f t _ hG).mp hw).differentiableAt
    · intro hf
      exact ⟨fun _ => deriv f t,
        (graphDerivativeRelation_realize_iff_of_local_graph G p f t _ hG).mpr hf.hasDerivAt⟩
  simp only [totalDerivativeGraph, mem_union, mem_setOf_eq, Sum.elim_comp_inl,
    Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, he,
    graphDerivativeRelation_realize_iff_of_local_graph G p f t d hG]
  constructor
  · rintro (hf | ⟨hf,rfl⟩)
    · exact hf.deriv.symm
    · exact (deriv_zero_of_not_differentiableAt hf).symm
  · intro h
    subst d
    by_cases hf : DifferentiableAt ℝ f t
    · exact Or.inl hf.hasDerivAt
    · exact Or.inr ⟨hf,deriv_zero_of_not_differentiableAt hf⟩

/-- In a horizontal section the frozen parameter is the vertical coordinate;
in a vertical section it is the horizontal coordinate. -/
def sectionGraph {α : Type} (axis : Bool) (G : Set (α ⊕ Fin 3 → ℝ)) :
    Set ((α ⊕ Unit) ⊕ Fin 2 → ℝ) :=
  {v | Sum.elim (fun c => v (Sum.inl (Sum.inl c)))
    ![(Preparation.sectionPoint axis (v (Sum.inl (Sum.inr ()))) (v (Sum.inr 0))).1,
      (Preparation.sectionPoint axis (v (Sum.inl (Sum.inr ()))) (v (Sum.inr 0))).2,
      v (Sum.inr 1)] ∈ G}

def liftSectionGraph {α : Type} (axis : Bool)
    (G : Set ((α ⊕ Unit) ⊕ Fin 2 → ℝ)) : Set (α ⊕ Fin 3 → ℝ) :=
  {v | Sum.elim
    (Sum.elim (v ∘ Sum.inl) (fun _ : Unit => v (Sum.inr (if axis then 1 else 0))))
    ![v (Sum.inr (if axis then 0 else 1)),v (Sum.inr 2)] ∈ G}

theorem sectionGraph_definable {α : Type} [Finite α]
    (axis : Bool) {G : Set (α ⊕ Fin 3 → ℝ)} (hG : RD G) : RD (sectionGraph axis G) := by
  let e : α ⊕ Fin 3 → (α ⊕ Unit) ⊕ Fin 2 := Sum.elim
    (Sum.inl ∘ Sum.inl) ![if axis then Sum.inr 0 else Sum.inl (Sum.inr ()),
      if axis then Sum.inl (Sum.inr ()) else Sum.inr 0, Sum.inr 1]
  convert hG.preimage_comp e using 1
  ext v
  have he : v ∘ e = Sum.elim (fun c => v (Sum.inl (Sum.inl c)))
    ![(Preparation.sectionPoint axis (v (Sum.inl (Sum.inr ()))) (v (Sum.inr 0))).1,
      (Preparation.sectionPoint axis (v (Sum.inl (Sum.inr ()))) (v (Sum.inr 0))).2, v (Sum.inr 1)] := by
    funext j
    rcases j with j | j
    · rfl
    · fin_cases j <;> cases axis <;> rfl
  simp only [sectionGraph, mem_setOf_eq, mem_preimage, he]

theorem liftSectionGraph_definable {α : Type} [Finite α]
    (axis : Bool) {G : Set ((α ⊕ Unit) ⊕ Fin 2 → ℝ)} (hG : RD G) :
    RD (liftSectionGraph axis G) := by
  let e : (α ⊕ Unit) ⊕ Fin 2 → α ⊕ Fin 3 := Sum.elim
    (Sum.elim Sum.inl (fun _ : Unit => Sum.inr (if axis then 1 else 0)))
    ![Sum.inr (if axis then 0 else 1),Sum.inr 2]
  convert hG.preimage_comp e using 1
  ext v
  have he : v ∘ e = Sum.elim
    (Sum.elim (v ∘ Sum.inl) (fun _ : Unit => v (Sum.inr (if axis then 1 else 0))))
    ![v (Sum.inr (if axis then 0 else 1)),v (Sum.inr 2)] := by
    funext j
    rcases j with (j | j) | j
    · rfl
    · rfl
    · fin_cases j <;> rfl
  simp only [liftSectionGraph, mem_setOf_eq, mem_preimage, he]

theorem sectionGraph_realize {α : Type} (axis : Bool) (G : Set (α ⊕ Fin 3 → ℝ))
    (p : α → ℝ) (u t z : ℝ) :
    Sum.elim (Sum.elim p (fun _ : Unit => u)) ![t,z] ∈ sectionGraph axis G ↔
      Sum.elim p ![(Preparation.sectionPoint axis u t).1,
        (Preparation.sectionPoint axis u t).2,z] ∈ G := by
  simp [sectionGraph, Function.comp_def]

theorem liftSectionGraph_realize {α : Type} (axis : Bool)
    (G : Set ((α ⊕ Unit) ⊕ Fin 2 → ℝ)) (p : α → ℝ) (u t z : ℝ) :
    Sum.elim p ![(Preparation.sectionPoint axis u t).1,
      (Preparation.sectionPoint axis u t).2,z] ∈ liftSectionGraph axis G ↔
      Sum.elim (Sum.elim p (fun _ : Unit => u)) ![t,z] ∈ G := by
  cases axis <;> simp [liftSectionGraph, Preparation.sectionPoint]

def partialGraph {α : Type} (axis : Bool) (G : Set (α ⊕ Fin 3 → ℝ)) :
    Set (α ⊕ Fin 3 → ℝ) := liftSectionGraph axis (totalDerivativeGraph (sectionGraph axis G))

theorem partialGraph_definable {α : Type} [Finite α] (axis : Bool)
    {G : Set (α ⊕ Fin 3 → ℝ)} (hG : RD G) : RD (partialGraph axis G) :=
  liftSectionGraph_definable axis (totalDerivativeGraph_definable (sectionGraph_definable axis hG))

def mixedJetGraph {α : Type} (G : Set (α ⊕ Fin 3 → ℝ)) (a b : ℕ) :
    Set (α ⊕ Fin 3 → ℝ) := (partialGraph false)^[b] ((partialGraph true)^[a] G)

theorem mixedJetGraph_definable {α : Type} [Finite α] {G : Set (α ⊕ Fin 3 → ℝ)}
    (hG : RD G) (a b : ℕ) : RD (mixedJetGraph G a b) := by
  have iter (axis : Bool) (n : ℕ) (H : Set (α ⊕ Fin 3 → ℝ)) (hH : RD H) :
      RD ((partialGraph axis)^[n] H) := by
    induction n with
    | zero => exact hH
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact partialGraph_definable axis ih
  exact iter false b _ (iter true a _ hG)

def RealizesOn {α : Type} (G : Set (α ⊕ Fin 3 → ℝ)) (p : α → ℝ)
    (f : ℝ × ℝ → ℝ) (R : Set (ℝ × ℝ)) : Prop :=
  ∀ x ∈ R, ∀ z, Sum.elim p ![x.1,x.2,z] ∈ G ↔ z = f x

theorem partialGraph_realizesOn {α : Type} {G : Set (α ⊕ Fin 3 → ℝ)}
    {p : α → ℝ} {f : ℝ × ℝ → ℝ} {R : Set (ℝ × ℝ)} (hR : IsOpen R)
    (hG : RealizesOn G p f R) (axis : Bool) :
    RealizesOn (partialGraph axis G) p (if axis then Preparation.derivX f else Preparation.derivY f) R := by
  intro x hx z
  let u := if axis then x.2 else x.1
  let t := if axis then x.1 else x.2
  have he : Preparation.sectionPoint axis u t = x := by cases axis <;> simp [u,t,Preparation.sectionPoint]
  have hc : Continuous (Preparation.sectionPoint axis u) := by
    cases axis
    · change Continuous (fun s : ℝ => (u,s))
      exact continuous_const.prodMk continuous_id
    · change Continuous (fun s : ℝ => (s,u))
      exact continuous_id.prodMk continuous_const
  have hloc : ∀ᶠ s in 𝓝 t, ∀ y, Sum.elim (Sum.elim p (fun _ : Unit => u)) ![s,y] ∈
      sectionGraph axis G ↔ y = f (Preparation.sectionPoint axis u s) := by
    have hn : ∀ᶠ s in 𝓝 t, Preparation.sectionPoint axis u s ∈ R :=
      hc.continuousAt (hR.mem_nhds (he ▸ hx))
    filter_upwards [hn] with s hs y
    exact (sectionGraph_realize axis G p u s y).trans (hG _ hs y)
  have h := totalDerivativeGraph_realize (sectionGraph axis G)
    (Sum.elim p (fun _ : Unit => u)) (fun s => f (Preparation.sectionPoint axis u s)) t z hloc
  rw [← he, partialGraph, liftSectionGraph_realize, h]
  cases axis <;> simp [Preparation.sectionPoint, Preparation.derivX, Preparation.derivY]

theorem mixedJetGraph_realizesOn {α : Type} {G : Set (α ⊕ Fin 3 → ℝ)}
    {p : α → ℝ} {f : ℝ × ℝ → ℝ} {R : Set (ℝ × ℝ)} (hR : IsOpen R)
    (hG : RealizesOn G p f R) (a b : ℕ) :
    RealizesOn (mixedJetGraph G a b) p (Preparation.mixedJet f a b) R := by
  have iter (axis : Bool) (n : ℕ) (H : Set (α ⊕ Fin 3 → ℝ)) (g : ℝ × ℝ → ℝ)
      (hH : RealizesOn H p g R) :
      RealizesOn ((partialGraph axis)^[n] H) p
        ((if axis then Preparation.derivX else Preparation.derivY)^[n] g) R := by
    induction n with
    | zero => exact hH
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      cases axis <;> simpa using partialGraph_realizesOn hR ih _
  exact iter false b _ _ (iter true a _ _ hG)

end PaperI.GoodStrips
