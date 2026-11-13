import PaperILean.JointCellAttachments
import PaperILean.FiniteDefinableSelection

/-! Whole-chain eligibility keeps the external parameter and both endpoints.
Finite-valued selection has definable fibers; it is not claimed continuous.
Cells are supplied as a fixed finite joint family, not extracted from the
pointwise cell-decomposition contract. Empty cells and zero-edge chains remain. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

abbrev BoundedCellChain (ι : Type*) [Fintype ι] :=
  Σ length : Fin (Fintype.card ι), Fin (length.val + 1) → ι

def cellChainEligibility {ρ κ ι : Type*} [Fintype ι]
    (C : ι → Set ((ρ ⊕ κ) → ℝ)) (c : BoundedCellChain ι) :
    Set (((ρ ⊕ κ) ⊕ κ) → ℝ) :=
  {q | (fun k => q (Sum.inl (Sum.inr k))) ∈
      projectionFiber (C (c.2 0)) (fun r => q (Sum.inl (Sum.inl r))) ∧
    (fun k => q (Sum.inr k)) ∈
      projectionFiber (C (c.2 (Fin.last c.1.val))) (fun r => q (Sum.inl (Sum.inl r))) ∧
    Function.Injective c.2 ∧
    ∀ k : Fin c.1.val,
      (closureAttachmentGraph (fun i => projectionFiber (C i)
        (fun r => q (Sum.inl (Sum.inl r))))).Adj (c.2 k.castSucc) (c.2 k.succ)}

theorem cellChainEligibility_definable {ρ κ ι : Type} [Finite ρ] [Fintype κ] [Fintype ι]
    (C : ι → Set ((ρ ⊕ κ) → ℝ))
    (hC : ∀ i, (univ : Set ℝ).Definable Language.ring (C i)) (c : BoundedCellChain ι) :
    (univ : Set ℝ).Definable Language.ring (cellChainEligibility C c) := by
  classical
  let ep : ρ → (ρ ⊕ κ) ⊕ κ := fun r => Sum.inl (Sum.inl r)
  let eb : ρ ⊕ κ → (ρ ⊕ κ) ⊕ κ := Sum.elim ep Sum.inr
  have ha := (hC (c.2 0)).preimage_comp (Sum.inl : ρ ⊕ κ → (ρ ⊕ κ) ⊕ κ)
  have hb := (hC (c.2 (Fin.last c.1.val))).preimage_comp eb
  have he : ∀ k : Fin c.1.val, (univ : Set ℝ).Definable Language.ring
      {q : ((ρ ⊕ κ) ⊕ κ) → ℝ |
        (closureAttachmentGraph (fun i => projectionFiber (C i) (q ∘ ep))).Adj
          (c.2 k.castSucc) (c.2 k.succ)} := by
    intro k
    by_cases hk : c.2 k.castSucc = c.2 k.succ
    · simpa only [hk, SimpleGraph.irrefl, Set.setOf_false] using
        (Set.definable_empty : (univ : Set ℝ).Definable Language.ring
          (∅ : Set (((ρ ⊕ κ) ⊕ κ) → ℝ)))
    · convert (cellAdjacencyParameterDomain_definable
        (hC (c.2 k.castSucc)) (hC (c.2 k.succ))).preimage_comp ep using 1
      ext q
      exact (cellAdjacencyParameterDomain_iff_adj C (q ∘ ep) hk).symm
  by_cases hinj : Function.Injective c.2
  · convert ha.inter (hb.inter (realDefinable_finite_all he)) using 1
    ext q
    simp only [cellChainEligibility, Set.mem_setOf_eq, hinj, true_and, Set.mem_inter_iff,
      Set.mem_preimage, projectionFiber, Function.comp_def, eb, ep]
    have ea : Sum.elim (fun r => q (Sum.inl (Sum.inl r)))
        (fun k => q (Sum.inl (Sum.inr k))) = (fun x => q (Sum.inl x)) := by
      funext x; cases x <;> rfl
    have eb' : Sum.elim (fun r => q (Sum.inl (Sum.inl r)))
        (fun k => q (Sum.inr k)) =
        (fun x => q (Sum.elim (fun r => Sum.inl (Sum.inl r)) Sum.inr x)) := by
      funext x; cases x <;> rfl
    rw [ea,eb']
  · have hempty : cellChainEligibility C c = ∅ := by
      ext q
      simp only [cellChainEligibility, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hinj h.2.2.1
    rw [hempty]
    exact Set.definable_empty

/-- A simple graph path supplies a finite code with the exact two endpoint cells. -/
theorem exists_cellChainEligibility_of_reachable {ρ κ ι : Type*} [Fintype ι]
    (C : ι → Set ((ρ ⊕ κ) → ℝ)) (p : ρ → ℝ) (a b : κ → ℝ)
    {i j : ι} (ha : a ∈ projectionFiber (C i) p) (hb : b ∈ projectionFiber (C j) p)
    (hij : (closureAttachmentGraph (fun k => projectionFiber (C k) p)).Reachable i j) :
    ∃ c : BoundedCellChain ι, Sum.elim (Sum.elim p a) b ∈ cellChainEligibility C c := by
  obtain ⟨w,hw⟩ := hij.exists_isPath
  let c : BoundedCellChain ι := ⟨⟨w.length,hw.length_lt⟩,fun k => w.getVert k.val⟩
  refine ⟨c,?_,?_,?_,?_⟩
  · change a ∈ projectionFiber (C (w.getVert 0)) p
    simpa only [SimpleGraph.Walk.getVert_zero] using ha
  · simpa only [c, Fin.val_last, SimpleGraph.Walk.getVert_length] using hb
  · intro k l h
    apply Fin.ext
    exact hw.getVert_injOn (by simpa only [Set.mem_setOf_eq] using Nat.le_of_lt_succ k.isLt)
      (by simpa only [Set.mem_setOf_eq] using Nat.le_of_lt_succ l.isLt) h
  · intro k
    exact w.adj_getVert_succ k.isLt

theorem connected_finite_cover_has_cellChainEligibility {ρ κ ι : Type*} [Fintype ι]
    (C : ι → Set ((ρ ⊕ κ) → ℝ)) (p : ρ → ℝ) (S : Set (κ → ℝ))
    (hS : IsPreconnected S) (hCS : ∀ i, projectionFiber (C i) p ⊆ S)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ projectionFiber (C i) p)
    (a b : κ → ℝ) (ha : a ∈ S) (hb : b ∈ S) :
    ∃ c : BoundedCellChain ι, Sum.elim (Sum.elim p a) b ∈ cellChainEligibility C c := by
  obtain ⟨i,hi⟩ := hcover a ha
  obtain ⟨j,hj⟩ := hcover b hb
  exact exists_cellChainEligibility_of_reachable C p a b hi hj
    (finite_cover_closureAttachment_reachable (fun k => projectionFiber (C k) p)
      S hS hCS hcover i j ⟨a,hi⟩ ⟨b,hj⟩)

/-- Joint selection of a whole simple chain, not separate edge choices.
Its length is strictly less than the supplied number of cell labels. -/
theorem joint_cellChain_selector {ρ κ ι : Type} [Finite ρ] [Fintype κ] [Fintype ι]
    (C : ι → Set ((ρ ⊕ κ) → ℝ))
    (hC : ∀ i, (univ : Set ℝ).Definable Language.ring (C i)) :
    ∃ pick : {q : ((ρ ⊕ κ) ⊕ κ) → ℝ // ∃ c, q ∈ cellChainEligibility C c} →
        BoundedCellChain ι,
      (∀ q, q.val ∈ cellChainEligibility C (pick q)) ∧
      ∀ c, (univ : Set ℝ).Definable Language.ring
        {q : ((ρ ⊕ κ) ⊕ κ) → ℝ |
          ∃ hq : ∃ d, q ∈ cellChainEligibility C d, pick ⟨q,hq⟩ = c} :=
  finite_definable_selector (cellChainEligibility C) (cellChainEligibility_definable C hC)

end PaperI
