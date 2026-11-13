import PaperILean.JointCellChainDomains

/-! A finite joint choice of the entire chain and every edge direction.
The direction selects actual-source-cell/target-fiber-closure attachments.
It may change between parameter regions; no global orientation is presumed. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

abbrev OrientedBoundedCellChain (ι : Type*) [Fintype ι] :=
  Σ c : BoundedCellChain ι, Fin c.1.val → Bool

def orientedCellChainSource {ι : Type*} [Fintype ι]
    (c : OrientedBoundedCellChain ι) (k : Fin c.1.1.val) : ι :=
  if c.2 k = true then c.1.2 k.castSucc else c.1.2 k.succ

def orientedCellChainTarget {ι : Type*} [Fintype ι]
    (c : OrientedBoundedCellChain ι) (k : Fin c.1.1.val) : ι :=
  if c.2 k = true then c.1.2 k.succ else c.1.2 k.castSucc

def orientedCellChainEligibility {ρ κ ι : Type*} [Fintype ι]
    (C : ι → Set ((ρ ⊕ κ) → ℝ)) (c : OrientedBoundedCellChain ι) :
    Set (((ρ ⊕ κ) ⊕ κ) → ℝ) :=
  cellChainEligibility C c.1 ∩
    {q | ∀ k : Fin c.1.1.val,
      (fun r => q (Sum.inl (Sum.inl r))) ∈
        directedCellAttachmentDomain (C (orientedCellChainSource c k))
          (C (orientedCellChainTarget c k))}

theorem orientedCellChainEligibility_definable
    {ρ κ ι : Type} [Finite ρ] [Fintype κ] [Fintype ι]
    (C : ι → Set ((ρ ⊕ κ) → ℝ))
    (hC : ∀ i, (univ : Set ℝ).Definable Language.ring (C i))
    (c : OrientedBoundedCellChain ι) :
    (univ : Set ℝ).Definable Language.ring (orientedCellChainEligibility C c) :=
  (cellChainEligibility_definable C hC c.1).inter
    (realDefinable_finite_all (fun k =>
      (directedCellAttachmentDomain_definable (hC (orientedCellChainSource c k))
        (hC (orientedCellChainTarget c k))).preimage_comp
          (fun r => Sum.inl (Sum.inl r))))

theorem cellChainEligibility_has_orientation {ρ κ ι : Type*} [Fintype ι]
    (C : ι → Set ((ρ ⊕ κ) → ℝ)) (c : BoundedCellChain ι)
    {q : ((ρ ⊕ κ) ⊕ κ) → ℝ} (hq : q ∈ cellChainEligibility C c) :
    ∃ σ : Fin c.1.val → Bool, q ∈ orientedCellChainEligibility C ⟨c,σ⟩ := by
  classical
  let p : ρ → ℝ := fun r => q (Sum.inl (Sum.inl r))
  let σ : Fin c.1.val → Bool := fun k => decide
    (p ∈ directedCellAttachmentDomain (C (c.2 k.castSucc)) (C (c.2 k.succ)))
  refine ⟨σ,hq,?_⟩
  intro k
  by_cases hk : p ∈ directedCellAttachmentDomain (C (c.2 k.castSucc)) (C (c.2 k.succ))
  · simp only [orientedCellChainSource, orientedCellChainTarget, σ, hk,
      decide_true, ↓reduceIte]
    exact hk
  · have hd := (hq.2.2.2 k).2
    have hr : p ∈ directedCellAttachmentDomain (C (c.2 k.succ)) (C (c.2 k.castSucc)) := by
      exact hd.resolve_left hk
    simp only [orientedCellChainSource, orientedCellChainTarget, σ, hk,
      decide_false, Bool.false_eq_true, ↓reduceIte]
    exact hr

/-- Jointly selected directions retain actual attachment witnesses. -/
theorem orientedCellChainEligibility_attachment {ρ κ ι : Type*} [Fintype ι]
    {C : ι → Set ((ρ ⊕ κ) → ℝ)} {c : OrientedBoundedCellChain ι}
    {q : ((ρ ⊕ κ) ⊕ κ) → ℝ} (hq : q ∈ orientedCellChainEligibility C c)
    (k : Fin c.1.1.val) :
    ∃ x, x ∈ projectionFiber (C (orientedCellChainSource c k))
      (fun r => q (Sum.inl (Sum.inl r))) ∧
      x ∈ closure (projectionFiber (C (orientedCellChainTarget c k))
        (fun r => q (Sum.inl (Sum.inl r)))) := hq.2 k

theorem joint_orientedCellChain_selector_on_connected_family
    {ρ κ ι : Type} [Finite ρ] [Fintype κ] [Fintype ι]
    (P : Set (ρ → ℝ)) (S : Set ((ρ ⊕ κ) → ℝ))
    (C : ι → Set ((ρ ⊕ κ) → ℝ))
    (hP : (univ : Set ℝ).Definable Language.ring P)
    (hS : (univ : Set ℝ).Definable Language.ring S)
    (hC : ∀ i, (univ : Set ℝ).Definable Language.ring (C i))
    (hconn : ∀ p ∈ P, IsPreconnected (projectionFiber S p))
    (hCS : ∀ p ∈ P, ∀ i, projectionFiber (C i) p ⊆ projectionFiber S p)
    (hcover : ∀ p ∈ P, ∀ x ∈ projectionFiber S p, ∃ i, x ∈ projectionFiber (C i) p) :
    ∃ pick : cellChainEndpointDomain P S → OrientedBoundedCellChain ι,
      (∀ q, q.val ∈ orientedCellChainEligibility C (pick q)) ∧
      ∀ c, (univ : Set ℝ).Definable Language.ring
        {q : ((ρ ⊕ κ) ⊕ κ) → ℝ |
          ∃ hq : q ∈ cellChainEndpointDomain P S, pick ⟨q,hq⟩ = c} := by
  apply finite_definable_selector_on (cellChainEndpointDomain P S)
    (orientedCellChainEligibility C) (cellChainEndpointDomain_definable hP hS)
    (orientedCellChainEligibility_definable C hC)
  intro q hq
  obtain ⟨c,hc⟩ := cellChainEndpointDomain_covered P S C hconn hCS hcover q hq
  obtain ⟨σ,hσ⟩ := cellChainEligibility_has_orientation C c hc
  exact ⟨⟨c,σ⟩,hσ⟩

end PaperI
