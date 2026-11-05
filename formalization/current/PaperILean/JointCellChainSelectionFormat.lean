import PaperILean.JointOrientedCellChains
import PaperILean.FiniteSelectorGraphs

/-! The selected complete chain has a real-coordinate semialgebraic graph
and a finite partition of the exact parameter/two-endpoint domain. Bounds
here are for the supplied family; ambient-input cell budgets remain separate. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem published_joint_orientedCellChain_selection_format
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ ι : Type} [Finite ρ] [Fintype κ] [Fintype ι]
    (P : Set (ρ → ℝ)) (S : Set ((ρ ⊕ κ) → ℝ))
    (C : ι → Set ((ρ ⊕ κ) → ℝ))
    (hP : HasPolynomialSignDescription P) (hS : HasPolynomialSignDescription S)
    (hC : ∀ i, HasPolynomialSignDescription (C i))
    (hconn : ∀ p ∈ P, IsPreconnected (projectionFiber S p))
    (hCS : ∀ p ∈ P, ∀ i, projectionFiber (C i) p ⊆ projectionFiber S p)
    (hcover : ∀ p ∈ P, ∀ x ∈ projectionFiber S p, ∃ i, x ∈ projectionFiber (C i) p) :
    ∃ (pick : cellChainEndpointDomain P S → OrientedBoundedCellChain ι) (s d : ℕ),
      (∀ q, q.val ∈ orientedCellChainEligibility C (pick q)) ∧
      (∀ c, ∃ A : Finset (MvPolynomial ((ρ ⊕ κ) ⊕ κ) ℝ),
        A.card ≤ s ∧ (∀ v ∈ A, v.totalDegree ≤ d) ∧
        PolynomialSignDetermined A
          {q : ((ρ ⊕ κ) ⊕ κ) → ℝ |
            ∃ hq : q ∈ cellChainEndpointDomain P S, pick ⟨q,hq⟩ = c}) ∧
      ∀ encode : OrientedBoundedCellChain ι → Unit → ℝ,
        HasPolynomialSignDescription
          (encodedFiniteSelectorGraph (cellChainEndpointDomain P S) pick encode) := by
  obtain ⟨pick,hpick,hfiber⟩ := joint_orientedCellChain_selector_on_connected_family
    P S C (hasPolynomialSignDescription_definable hP) (hasPolynomialSignDescription_definable hS)
    (fun i => hasPolynomialSignDescription_definable (hC i)) hconn hCS hcover
  obtain ⟨s,d,hformat⟩ := finite_sign_descriptions_common_format _
    (fun c => hQE.finite_sign_description _ (hfiber c))
  exact ⟨pick,s,d,hpick,hformat,
    fun encode => published_encodedFiniteSelectorGraph_semialgebraic hQE _ pick encode hfiber⟩

/-- The first/last cells contain the actual endpoints, each directed attachment
has a source in the ambient fiber, and the whole selected chain is simple. -/
theorem orientedCellChainEligibility_geometry {ρ κ ι : Type*} [Fintype ι]
    {P : Set (ρ → ℝ)} {S : Set ((ρ ⊕ κ) → ℝ)}
    {C : ι → Set ((ρ ⊕ κ) → ℝ)}
    (hCS : ∀ p ∈ P, ∀ i, projectionFiber (C i) p ⊆ projectionFiber S p)
    {q : ((ρ ⊕ κ) ⊕ κ) → ℝ} (hq : q ∈ cellChainEndpointDomain P S)
    {c : OrientedBoundedCellChain ι} (hc : q ∈ orientedCellChainEligibility C c) :
    c.1.1.val < Fintype.card ι ∧ Function.Injective c.1.2 ∧
    (fun k => q (Sum.inl (Sum.inr k))) ∈ projectionFiber (C (c.1.2 0))
      (fun r => q (Sum.inl (Sum.inl r))) ∧
    (fun k => q (Sum.inr k)) ∈ projectionFiber (C (c.1.2 (Fin.last c.1.1.val)))
      (fun r => q (Sum.inl (Sum.inl r))) ∧
    ∀ k : Fin c.1.1.val, ∃ x ∈ projectionFiber S (fun r => q (Sum.inl (Sum.inl r))),
      x ∈ projectionFiber (C (orientedCellChainSource c k))
        (fun r => q (Sum.inl (Sum.inl r))) ∧
      x ∈ closure (projectionFiber (C (orientedCellChainTarget c k))
        (fun r => q (Sum.inl (Sum.inl r)))) := by
  refine ⟨c.1.1.isLt,hc.1.2.2.1,hc.1.1,hc.1.2.1,?_⟩
  intro k
  obtain ⟨x,hsrc,htgt⟩ := orientedCellChainEligibility_attachment hc k
  exact ⟨x,hCS _ hq.1 _ hsrc,hsrc,htgt⟩

end PaperI
