import PaperILean.PublishedFiniteConnectedCover
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

/-! Elementary topology of scalar frontiers. Pre-strategy boundary checks were
executed in checkpoint_108_017_scalar_frontier_prestrategy.log. No nonempty,
closedness, boundedness, or positive-dimensional hypothesis is imposed. -/
noncomputable section
namespace PaperI
open Set

theorem finite_frontier_inter {S T : Set ℝ}
    (hS : (frontier S).Finite) (hT : (frontier T).Finite) :
    (frontier (S ∩ T)).Finite := by
  apply (hS.union hT).subset
  intro x hx
  rcases frontier_inter_subset S T hx with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2

theorem finite_frontier_union {S T : Set ℝ}
    (hS : (frontier S).Finite) (hT : (frontier T).Finite) :
    (frontier (S ∪ T)).Finite := by
  apply (hS.union hT).subset
  intro x hx
  rcases frontier_union_subset S T hx with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2

theorem finite_frontier_of_isPreconnected {S : Set ℝ} (hS : IsPreconnected S) :
    (frontier S).Finite := by
  have hc (a : ℝ) : (frontier (Ici a)).Finite := by simp [frontier_Ici]
  have ho (a : ℝ) : (frontier (Ioi a)).Finite := by simp [frontier_Ioi]
  have hc' (a : ℝ) : (frontier (Iic a)).Finite := by simp [frontier_Iic]
  have ho' (a : ℝ) : (frontier (Iio a)).Finite := by simp [frontier_Iio]
  have h := hS.mem_intervals
  simp only [mem_insert_iff, mem_singleton_iff] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · rw [h, ← Ici_inter_Iic]; exact finite_frontier_inter (hc _) (hc' _)
  · rw [h, ← Ici_inter_Iio]; exact finite_frontier_inter (hc _) (ho' _)
  · rw [h, ← Ioi_inter_Iic]; exact finite_frontier_inter (ho _) (hc' _)
  · rw [h, ← Ioi_inter_Iio]; exact finite_frontier_inter (ho _) (ho' _)
  · rw [h]; exact hc _
  · rw [h]; exact ho _
  · rw [h]; exact hc' _
  · rw [h]; exact ho' _
  · simp [h]
  · simp [h]

theorem finite_frontier_finset_biUnion {ι : Type*} (s : Finset ι)
    (U : ι → Set ℝ) (hU : ∀ i ∈ s, (frontier (U i)).Finite) :
    (frontier (⋃ i ∈ s, U i)).Finite := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact finite_frontier_union (hU a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hU i (Finset.mem_insert_of_mem hi)))

theorem finite_frontier_finite_preconnected_cover {ι : Type*} [Fintype ι]
    (U : ι → Set ℝ) (hU : ∀ i, IsPreconnected (U i)) :
    (frontier (⋃ i, U i)).Finite := by
  simpa using finite_frontier_finset_biUnion Finset.univ U
    (fun i _ => finite_frontier_of_isPreconnected (hU i))

theorem preconnected_subset_or_subset_compl_of_avoids_frontier
    {J S : Set ℝ} (hJ : IsPreconnected J)
    (havoid : ∀ x ∈ J, x ∉ frontier S) : J ⊆ S ∨ J ⊆ Sᶜ := by
  have hcover : J ⊆ interior S ∪ interior Sᶜ := by
    intro x hx
    by_cases hs : x ∈ closure S
    · have hi : x ∈ interior S := by
        by_contra hn
        exact havoid x hx ⟨hs, hn⟩
      exact Or.inl hi
    · exact Or.inr (by simpa only [interior_compl, mem_compl_iff] using hs)
  have hd : Disjoint (interior S) (interior Sᶜ) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (interior_subset hy) (interior_subset hx)
  rcases hJ.subset_or_subset isOpen_interior isOpen_interior hd hcover with h | h
  · exact Or.inl (h.trans interior_subset)
  · exact Or.inr (h.trans interior_subset)

theorem preconnected_subset_of_avoids_frontier_of_mem
    {J S : Set ℝ} (hJ : IsPreconnected J)
    (havoid : ∀ x ∈ J, x ∉ frontier S)
    (hmeet : ∃ x ∈ J, x ∈ S) : J ⊆ S := by
  rcases preconnected_subset_or_subset_compl_of_avoids_frontier hJ havoid with h | h
  · exact h
  · obtain ⟨x,hx,hs⟩ := hmeet
    exact False.elim (h hx hs)

end PaperI
