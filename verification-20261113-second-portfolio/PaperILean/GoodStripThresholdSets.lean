import PaperILean.GoodStripFormat

noncomputable section

namespace PaperI.GoodStrips

open Set FirstOrder Filter MeasureTheory
open scoped Topology ENNReal

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private abbrev RD {α : Type} (S : Set (α → ℝ)) :=
  (univ : Set ℝ).Definable Language.ring S

private theorem definable_finite_exists {β κ : Type} [Fintype κ]
    {P : κ → (β → ℝ) → Prop}
    (hP : ∀ k, RD {v | P k v}) : RD {v | ∃ k, P k v} := by
  classical
  have h := (realDefinable_finite_all fun k => (hP k).compl).compl
  convert h using 1
  ext v
  simp only [mem_setOf_eq,mem_compl_iff,not_forall,not_not]

abbrev ThresholdIndex (ι : Type) (N : ℕ) := ι × Fin (N+1) × Fin (N+1)

abbrev ThresholdParam (α ι : Type) (N : ℕ) := α ⊕ (ThresholdIndex ι N ⊕ ι)

def thresholdPlane {α : Type} (G : Set (α ⊕ Fin 3 → ℝ)) (T : α)
    (upper : Bool) : Set (α ⊕ Fin 2 → ℝ) :=
  {v | ∃ z : ℝ, Sum.elim (v ∘ Sum.inl) ![v (Sum.inr 0),v (Sum.inr 1),z] ∈ G ∧
    if upper then |z| < v (Sum.inl T) else v (Sum.inl T) < |z|}

theorem thresholdPlane_definable {α : Type} [Finite α]
    {G : Set (α ⊕ Fin 3 → ℝ)} (hG : RD G) (T : α) (upper : Bool) :
    RD (thresholdPlane G T upper) := by
  let β := α ⊕ Fin 2
  let γ := β ⊕ Unit
  let e : α ⊕ Fin 3 → γ := Sum.elim (Sum.inl ∘ Sum.inl)
    ![Sum.inl (Sum.inr 0),Sum.inl (Sum.inr 1),Sum.inr ()]
  let z : MvPolynomial γ ℝ := MvPolynomial.X (Sum.inr ())
  let t : MvPolynomial γ ℝ := MvPolynomial.X (Sum.inl (Sum.inl T))
  have hC : RD {v : γ → ℝ | if upper then |v (Sum.inr ())| < v (Sum.inl (Sum.inl T))
      else v (Sum.inl (Sum.inl T)) < |v (Sum.inr ())|} := by
    cases upper
    · have h := (realPolynomial_lt_definable t z).union (realPolynomial_lt_definable t (-z))
      convert h using 1
      ext v
      simp only [Bool.false_eq_true, if_false, mem_setOf_eq, mem_union, t, z,
        MvPolynomial.eval_X, map_neg]
      rw [abs_eq_max_neg, lt_max_iff]
    · have h := (realPolynomial_lt_definable z t).inter (realPolynomial_lt_definable (-z) t)
      convert h using 1
      ext v
      simp only [Bool.true_eq, if_true, mem_setOf_eq, mem_inter_iff, t, z,
        MvPolynomial.eval_X, map_neg]
      rw [abs_eq_max_neg, max_lt_iff]
  have hE := realDefinable_exists ((hG.preimage_comp e).inter hC)
  convert hE using 1
  ext v
  have he (w : Unit → ℝ) : Sum.elim v w ∘ e =
      Sum.elim (v ∘ Sum.inl) ![v (Sum.inr 0),v (Sum.inr 1),w ()] := by
    funext i
    rcases i with i | i
    · rfl
    · fin_cases i <;> rfl
  simp only [thresholdPlane,mem_setOf_eq,mem_inter_iff,mem_preimage,he,Sum.elim_inl,Sum.elim_inr]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨fun _ => x,by simpa only [he,mem_setOf_eq,Sum.elim_inl,Sum.elim_inr] using hx⟩
  · rintro ⟨w,hw⟩
    exact ⟨w (),by simpa only [he,mem_setOf_eq,Sum.elim_inl,Sum.elim_inr] using hw⟩

theorem thresholdPlane_value {α : Type} {G : Set (α ⊕ Fin 3 → ℝ)} (T : α)
    (upper : Bool) {p : α → ℝ} {f : ℝ × ℝ → ℝ} {R : Set (ℝ × ℝ)}
    (hf : RealizesOn G p f R) {x : ℝ × ℝ} (hx : x ∈ R) :
    x ∈ planeFiber (thresholdPlane G T upper) p ↔
      if upper then |f x| < p T else p T < |f x| := by
  change (∃ z : ℝ, Sum.elim p ![x.1,x.2,z] ∈ G ∧
    if upper then |z| < p T else p T < |z|) ↔ _
  constructor
  · rintro ⟨z,hz,hz'⟩
    exact ((hf x hx z).mp hz) ▸ hz'
  · intro h
    exact ⟨f x,(hf x hx _).mpr rfl,h⟩

def hGoodFamily {α ι : Type} (U : Set (α ⊕ Fin 2 → ℝ))
    (G : ι → Set (α ⊕ Fin 3 → ℝ)) (N : ℕ) :
    Set (ThresholdParam α ι N ⊕ Fin 2 → ℝ) :=
  parameterPlaneLift Sum.inl U ∩
    {v | ∀ i (a : Fin (N+1)), 0 < v (Sum.inl (Sum.inr (Sum.inr i))) →
      v ∈ thresholdPlane (parameterGraphLift Sum.inl (mixedJetGraph (G i) a 0))
        (Sum.inr (Sum.inl (i,a,0))) true}

theorem hGoodFamily_definable {α ι : Type} [Finite α] [Fintype ι]
    {U : Set (α ⊕ Fin 2 → ℝ)} {G : ι → Set (α ⊕ Fin 3 → ℝ)}
    (hU : RD U) (hG : ∀ i, RD (G i)) (N : ℕ) : RD (hGoodFamily U G N) := by
  apply (parameterPlaneLift_definable Sum.inl hU).inter
  apply realDefinable_finite_all
  intro i
  apply realDefinable_finite_all
  intro a
  have hp := realPolynomial_lt_definable 0
    (MvPolynomial.X (Sum.inl (Sum.inr (Sum.inr i)) : ThresholdParam α ι N ⊕ Fin 2))
  have ht := thresholdPlane_definable
    (parameterGraphLift_definable Sum.inl (mixedJetGraph_definable (hG i) a 0))
    (Sum.inr (Sum.inl (i,a,0)) : ThresholdParam α ι N) true
  convert hp.compl.union ht using 1
  ext v
  classical
  simp only [mem_setOf_eq,mem_union,mem_compl_iff,map_zero,MvPolynomial.eval_X]
  tauto

private theorem parameterGraphLift_realizes {ρ α : Type} (e : ρ → α)
    {G : Set (ρ ⊕ Fin 3 → ℝ)} {p : α → ℝ} {f : ℝ × ℝ → ℝ} {R : Set (ℝ × ℝ)}
    (hG : RealizesOn G (p ∘ e) f R) :
    RealizesOn (parameterGraphLift e G) p f R := by
  intro x hx z
  exact (parameterGraphLift_value e G p x z).trans (hG x hx z)

def hGoodParameter {α ι : Type} {N : ℕ}
    (p : α → ℝ) (A : ι → ℝ) (C L : ℝ) : ThresholdParam α ι N → ℝ :=
  Sum.elim p (Sum.elim (fun j => C*A j.1/L^j.2.1.val) A)

theorem hGoodFamily_fiber {α ι : Type} {N : ℕ}
    {U : Set (α ⊕ Fin 2 → ℝ)} {G : ι → Set (α ⊕ Fin 3 → ℝ)} {p : α → ℝ}
    {f : ι → ℝ × ℝ → ℝ} {R : Set (ℝ × ℝ)} (hR : IsOpen R)
    (hsub : planeFiber U p ⊆ R) (hG : ∀ i, RealizesOn (G i) p (f i) R)
    (A : ι → ℝ) (C L : ℝ) :
    planeFiber (hGoodFamily U G N) (hGoodParameter p A C L) =
      horizontalGoodOn (planeFiber U p) f N A C L := by
  let q := hGoodParameter (N := N) p A C L
  have hqp : q ∘ Sum.inl = p := rfl
  change planeFiber (hGoodFamily U G N) q = _
  rw [hGoodFamily,planeFiber_inter,parameterPlaneLift_fiber,hqp]
  ext x
  change (x ∈ planeFiber U p ∧ ∀ i (a : Fin (N+1)), 0 < A i →
      x ∈ planeFiber
        (thresholdPlane (parameterGraphLift Sum.inl (mixedJetGraph (G i) a 0))
          (Sum.inr (Sum.inl (i,a,0))) true) q) ↔
    (x ∈ planeFiber U p ∧ ∀ i (a : Fin (N+1)), 0 < A i →
      |Jet (f i) a.val 0 x| < C*A i/L^a.val)
  apply and_congr_right
  intro hx
  apply forall_congr'
  intro i
  apply forall_congr'
  intro a
  apply imp_congr_right
  intro _
  have hh := mixedJetGraph_realizesOn hR (hG i) a 0
  have hq : RealizesOn (parameterGraphLift Sum.inl (mixedJetGraph (G i) a 0)) q
      (Jet (f i) a 0) R := by apply parameterGraphLift_realizes; rwa [hqp]
  exact thresholdPlane_value _ true hq (hsub hx)

def vBadFamily {α ι : Type} (V : Set (α ⊕ Fin 2 → ℝ))
    (G : ι → Set (α ⊕ Fin 3 → ℝ)) (N a : ℕ) :
    Set ((α ⊕ ThresholdIndex ι N) ⊕ Fin 2 → ℝ) :=
  parameterPlaneLift Sum.inl V ∩
    {v | ∃ (i : ι) (b : Fin (N+1)), b.val ≤ N-a ∧
      v ∈ thresholdPlane (parameterGraphLift Sum.inl (mixedJetGraph (G i) a b))
        (Sum.inr (i,0,b)) false}

theorem vBadFamily_definable {α ι : Type} [Finite α] [Fintype ι]
    {V : Set (α ⊕ Fin 2 → ℝ)} {G : ι → Set (α ⊕ Fin 3 → ℝ)}
    (hV : RD V) (hG : ∀ i, RD (G i)) (N a : ℕ) : RD (vBadFamily V G N a) := by
  apply (parameterPlaneLift_definable Sum.inl hV).inter
  apply definable_finite_exists
  intro i
  apply definable_finite_exists
  intro b
  by_cases hb : b.val ≤ N-a
  · simpa only [hb,true_and] using thresholdPlane_definable
      (parameterGraphLift_definable Sum.inl (mixedJetGraph_definable (hG i) a b))
      (Sum.inr (i,0,b) : α ⊕ ThresholdIndex ι N) false
  · simp only [hb,false_and,setOf_false]
    exact Set.definable_empty

theorem vBadFamily_fiber {α ι : Type} {N a : ℕ}
    {V : Set (α ⊕ Fin 2 → ℝ)} {G : ι → Set (α ⊕ Fin 3 → ℝ)} {p : α → ℝ}
    {f : ι → ℝ × ℝ → ℝ} {R : Set (ℝ × ℝ)} (hR : IsOpen R)
    (hsub : planeFiber V p ⊆ R) (hG : ∀ i, RealizesOn (G i) p (f i) R)
    (A : ι → ℝ) (C L W : ℝ) :
    planeFiber (vBadFamily V G N a)
        (Sum.elim p (fun j => C*A j.1/(L^a*W^j.2.2.val))) =
      verticalBadOn (planeFiber V p) f N a A C L W := by
  let q : (α ⊕ ThresholdIndex ι N) → ℝ :=
    Sum.elim p (fun j => C*A j.1/(L^a*W^j.2.2.val))
  change planeFiber (vBadFamily V G N a) q = _
  have hqp : q ∘ Sum.inl = p := rfl
  rw [vBadFamily,planeFiber_inter,parameterPlaneLift_fiber,hqp]
  ext x
  change (x ∈ planeFiber V p ∧ ∃ (i : ι) (b : Fin (N+1)), b.val ≤ N-a ∧
      x ∈ planeFiber
        (thresholdPlane (parameterGraphLift Sum.inl (mixedJetGraph (G i) a b))
          (Sum.inr (i,0,b)) false) q) ↔
    (x ∈ planeFiber V p ∧ ∃ i,∃ b ≤ N-a, C*A i/(L^a*W^b) < |Jet (f i) a b x|)
  apply and_congr_right
  intro hx
  have hh (i : ι) (b : Fin (N+1)) :
      x ∈ planeFiber
        (thresholdPlane (parameterGraphLift Sum.inl (mixedJetGraph (G i) a b))
          (Sum.inr (i,0,b)) false) q ↔ C*A i/(L^a*W^b.val) < |Jet (f i) a b.val x| := by
    have hj := mixedJetGraph_realizesOn hR (hG i) a b
    have hq : RealizesOn (parameterGraphLift Sum.inl (mixedJetGraph (G i) a b)) q
        (Jet (f i) a b) R := by apply parameterGraphLift_realizes; rwa [hqp]
    exact thresholdPlane_value _ false hq (hsub hx)
  constructor
  · rintro ⟨i,b,hb,hhb⟩
    exact ⟨i,b.val,hb,(hh i b).mp hhb⟩
  · rintro ⟨i,b,hb,hhb⟩
    let j : Fin (N+1) := ⟨b,by omega⟩
    exact ⟨i,j,hb,(hh i j).mpr hhb⟩

end PaperI.GoodStrips
