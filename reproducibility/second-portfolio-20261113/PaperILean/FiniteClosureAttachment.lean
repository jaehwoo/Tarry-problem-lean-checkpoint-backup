import Mathlib.Topology.Connected.Basic
import Mathlib.Combinatorics.SimpleGraph.Path

/-! The finite cell-chain step of I654. An attachment belongs to an actual
cell and to the closure of the other cell. Intersections of two closures are
not used. The cover may overlap and may contain empty pieces; only the two
endpoint pieces need be nonempty. No connectedness of individual pieces,
compactness, frontier condition, or choice of boundary chart extension is used.
Pre-strategy evidence: checkpoint_113_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set

def closureAttachmentGraph {X ι : Type*} [TopologicalSpace X]
    (C : ι → Set X) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ ((C i ∩ closure (C j)).Nonempty ∨
    (C j ∩ closure (C i)).Nonempty)
  symm := by
    intro i j h
    exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    intro i h
    exact h.1 rfl

theorem closureAttachmentGraph_adj_iff {X ι : Type*} [TopologicalSpace X]
    (C : ι → Set X) (i j : ι) :
    (closureAttachmentGraph C).Adj i j ↔ i ≠ j ∧
      ((C i ∩ closure (C j)).Nonempty ∨ (C j ∩ closure (C i)).Nonempty) := Iff.rfl

theorem closureAttachmentGraph_adj_nonempty {X ι : Type*} [TopologicalSpace X]
    {C : ι → Set X} {i j : ι} (h : (closureAttachmentGraph C).Adj i j) :
    (C i).Nonempty ∧ (C j).Nonempty := by
  rcases h.2 with ⟨x,hi,hj⟩ | ⟨x,hj,hi⟩
  · exact ⟨⟨x,hi⟩,closure_nonempty_iff.mp ⟨x,hj⟩⟩
  · exact ⟨closure_nonempty_iff.mp ⟨x,hi⟩,⟨x,hj⟩⟩

theorem closureAttachmentGraph_reachable_of_mem_closure
    {X ι : Type*} [TopologicalSpace X] (C : ι → Set X)
    {i j : ι} {x : X} (hi : x ∈ C i) (hj : x ∈ closure (C j)) :
    (closureAttachmentGraph C).Reachable i j := by
  by_cases h : i = j
  · subst j
    exact SimpleGraph.Reachable.refl i
  · exact SimpleGraph.Adj.reachable (G := closureAttachmentGraph C)
      ⟨h,Or.inl ⟨x,hi,hj⟩⟩

theorem closureAttachmentGraph_attachment_in_set
    {X ι : Type*} [TopologicalSpace X] {C : ι → Set X} {S : Set X}
    (hCS : ∀ i, C i ⊆ S) {i j : ι} (h : (closureAttachmentGraph C).Adj i j) :
    ∃ x ∈ S, (x ∈ C i ∧ x ∈ closure (C j)) ∨
      (x ∈ C j ∧ x ∈ closure (C i)) := by
  rcases h.2 with ⟨x,hi,hj⟩ | ⟨x,hj,hi⟩
  · exact ⟨x,hCS i hi,Or.inl ⟨hi,hj⟩⟩
  · exact ⟨x,hCS j hj,Or.inr ⟨hj,hi⟩⟩

/-- Finite closed separation proves reachability between nonempty cover pieces.
No conclusion about an isolated empty vertex is asserted. -/
theorem finite_cover_closureAttachment_reachable
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (C : ι → Set X) (S : Set X) (hS : IsPreconnected S)
    (hCS : ∀ i, C i ⊆ S) (hcover : ∀ x ∈ S, ∃ i, x ∈ C i)
    (i j : ι) (hi : (C i).Nonempty) (hj : (C j).Nonempty) :
    (closureAttachmentGraph C).Reachable i j := by
  classical
  by_contra hnot
  let R : ι → Prop := fun k => (closureAttachmentGraph C).Reachable i k
  let U : Set X := ⋃ k : {k // R k}, closure (C k.val)
  let V : Set X := ⋃ k : {k // ¬ R k}, closure (C k.val)
  have hU : IsClosed U := isClosed_iUnion_of_finite fun _ => isClosed_closure
  have hV : IsClosed V := isClosed_iUnion_of_finite fun _ => isClosed_closure
  have hUV : S ⊆ U ∪ V := by
    intro x hx
    obtain ⟨k,hk⟩ := hcover x hx
    by_cases hr : R k
    · exact Or.inl (mem_iUnion.mpr ⟨⟨k,hr⟩,subset_closure hk⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k,hr⟩,subset_closure hk⟩)
  have hSU : (S ∩ U).Nonempty := by
    obtain ⟨x,hx⟩ := hi
    exact ⟨x,hCS i hx,mem_iUnion.mpr
      ⟨⟨i,SimpleGraph.Reachable.refl i⟩,subset_closure hx⟩⟩
  have hSV : (S ∩ V).Nonempty := by
    obtain ⟨x,hx⟩ := hj
    exact ⟨x,hCS j hx,mem_iUnion.mpr ⟨⟨j,hnot⟩,subset_closure hx⟩⟩
  obtain ⟨x,hxS,hxU,hxV⟩ := isPreconnected_closed_iff.mp hS U V hU hV hUV hSU hSV
  obtain ⟨k,hk⟩ := hcover x hxS
  obtain ⟨u,hu⟩ := mem_iUnion.mp hxU
  obtain ⟨v,hv⟩ := mem_iUnion.mp hxV
  have hrk : R k := u.property.trans
    (closureAttachmentGraph_reachable_of_mem_closure C hk hu).symm
  exact v.property (hrk.trans (closureAttachmentGraph_reachable_of_mem_closure C hk hv))

/-- The simple chain has fewer edges than cover pieces; every attachment lies
in S. This numeric bound does not supply a jointly semialgebraic chain choice. -/
theorem finite_cover_exists_bounded_attachment_chain
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (C : ι → Set X) (S : Set X) (hS : IsPreconnected S)
    (hCS : ∀ i, C i ⊆ S) (hcover : ∀ x ∈ S, ∃ i, x ∈ C i)
    (i j : ι) (hi : (C i).Nonempty) (hj : (C j).Nonempty) :
    ∃ w : (closureAttachmentGraph C).Walk i j,
      w.IsPath ∧ w.length < Fintype.card ι ∧
        ∀ k < w.length, ∃ x ∈ S,
          (x ∈ C (w.getVert k) ∧ x ∈ closure (C (w.getVert (k+1)))) ∨
          (x ∈ C (w.getVert (k+1)) ∧ x ∈ closure (C (w.getVert k))) := by
  obtain ⟨w,hw⟩ := (finite_cover_closureAttachment_reachable C S hS hCS hcover i j hi hj).exists_isPath
  exact ⟨w,hw,hw.length_lt,fun k hk =>
    closureAttachmentGraph_attachment_in_set hCS (w.adj_getVert_succ hk)⟩

end PaperI
