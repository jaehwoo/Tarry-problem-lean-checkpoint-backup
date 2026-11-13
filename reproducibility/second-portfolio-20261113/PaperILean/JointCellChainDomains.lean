import PaperILean.JointCellChains

/-! The selector is now on the manuscript's actual parameter/two-endpoint
domain for a supplied finite joint cover. Connectedness is required only at
eligible parameters. No parameter-continuity or cell-chart data are assumed. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def cellChainEndpointDomain {ρ κ : Type*}
    (P : Set (ρ → ℝ)) (S : Set ((ρ ⊕ κ) → ℝ)) :
    Set (((ρ ⊕ κ) ⊕ κ) → ℝ) :=
  {q | (fun r => q (Sum.inl (Sum.inl r))) ∈ P ∧
    (fun k => q (Sum.inl (Sum.inr k))) ∈
      projectionFiber S (fun r => q (Sum.inl (Sum.inl r))) ∧
    (fun k => q (Sum.inr k)) ∈
      projectionFiber S (fun r => q (Sum.inl (Sum.inl r)))}

theorem cellChainEndpointDomain_definable {ρ κ : Type*}
    {P : Set (ρ → ℝ)} {S : Set ((ρ ⊕ κ) → ℝ)}
    (hP : (univ : Set ℝ).Definable Language.ring P)
    (hS : (univ : Set ℝ).Definable Language.ring S) :
    (univ : Set ℝ).Definable Language.ring (cellChainEndpointDomain P S) := by
  let ep : ρ → (ρ ⊕ κ) ⊕ κ := fun r => Sum.inl (Sum.inl r)
  let eb : ρ ⊕ κ → (ρ ⊕ κ) ⊕ κ := Sum.elim ep Sum.inr
  convert (hP.preimage_comp ep).inter
    ((hS.preimage_comp (Sum.inl : ρ ⊕ κ → (ρ ⊕ κ) ⊕ κ)).inter
      (hS.preimage_comp eb)) using 1
  ext q
  have ea : Sum.elim (fun r => q (Sum.inl (Sum.inl r)))
      (fun k => q (Sum.inl (Sum.inr k))) = q ∘ Sum.inl := by
    funext x; cases x <;> rfl
  have eb' : Sum.elim (fun r => q (Sum.inl (Sum.inl r)))
      (fun k => q (Sum.inr k)) = q ∘ eb := by
    funext x; cases x <;> rfl
  simp only [cellChainEndpointDomain, projectionFiber, Set.mem_setOf_eq,
    Set.mem_inter_iff, Set.mem_preimage, ea, eb']
  rfl

theorem cellChainEndpointDomain_covered {ρ κ ι : Type*} [Fintype ι]
    (P : Set (ρ → ℝ)) (S : Set ((ρ ⊕ κ) → ℝ))
    (C : ι → Set ((ρ ⊕ κ) → ℝ))
    (hconn : ∀ p ∈ P, IsPreconnected (projectionFiber S p))
    (hCS : ∀ p ∈ P, ∀ i, projectionFiber (C i) p ⊆ projectionFiber S p)
    (hcover : ∀ p ∈ P, ∀ x ∈ projectionFiber S p, ∃ i, x ∈ projectionFiber (C i) p) :
    ∀ q ∈ cellChainEndpointDomain P S, ∃ c, q ∈ cellChainEligibility C c := by
  intro q hq
  obtain ⟨c,hc⟩ := connected_finite_cover_has_cellChainEligibility C
    (fun r => q (Sum.inl (Sum.inl r))) _ (hconn _ hq.1) (hCS _ hq.1) (hcover _ hq.1)
    (fun k => q (Sum.inl (Sum.inr k))) (fun k => q (Sum.inr k)) hq.2.1 hq.2.2
  have he : Sum.elim (Sum.elim (fun r => q (Sum.inl (Sum.inl r)))
      (fun k => q (Sum.inl (Sum.inr k)))) (fun k => q (Sum.inr k)) = q := by
    funext i; rcases i with (r | k) | k <;> rfl
  exact ⟨c,he ▸ hc⟩

/-- This is a joint chain selector on exactly P and the two actual fiber
endpoints. The only decomposition premise is the displayed finite joint cover. -/
theorem joint_cellChain_selector_on_connected_family
    {ρ κ ι : Type} [Finite ρ] [Fintype κ] [Fintype ι]
    (P : Set (ρ → ℝ)) (S : Set ((ρ ⊕ κ) → ℝ))
    (C : ι → Set ((ρ ⊕ κ) → ℝ))
    (hP : (univ : Set ℝ).Definable Language.ring P)
    (hS : (univ : Set ℝ).Definable Language.ring S)
    (hC : ∀ i, (univ : Set ℝ).Definable Language.ring (C i))
    (hconn : ∀ p ∈ P, IsPreconnected (projectionFiber S p))
    (hCS : ∀ p ∈ P, ∀ i, projectionFiber (C i) p ⊆ projectionFiber S p)
    (hcover : ∀ p ∈ P, ∀ x ∈ projectionFiber S p, ∃ i, x ∈ projectionFiber (C i) p) :
    ∃ pick : cellChainEndpointDomain P S → BoundedCellChain ι,
      (∀ q, q.val ∈ cellChainEligibility C (pick q)) ∧
      ∀ c, (univ : Set ℝ).Definable Language.ring
        {q : ((ρ ⊕ κ) ⊕ κ) → ℝ |
          ∃ hq : q ∈ cellChainEndpointDomain P S, pick ⟨q,hq⟩ = c} :=
  finite_definable_selector_on (cellChainEndpointDomain P S) (cellChainEligibility C)
    (cellChainEndpointDomain_definable hP hS) (cellChainEligibility_definable C hC)
    (cellChainEndpointDomain_covered P S C hconn hCS hcover)

end PaperI
