import PaperILean.CommonMonotonePartition
import Mathlib.SetTheory.Cardinal.Finite

/-! An actual interval cut set from finitely many finite exceptional sets.
Exceptional points outside the interval are filtered out, endpoints are added,
and the count includes all families. Empty families and degenerate intervals
are permitted. This lemma supplies no finiteness assumption by itself. -/

noncomputable section
namespace PaperI
open Set
open scoped BigOperators

theorem exists_interval_cut_set_of_finite_bad_sets
    {ι : Type*} [Fintype ι] (bad : ι → Set ℝ) (K : ι → ℕ)
    (hfin : ∀ i, (bad i).Finite) (hcard : ∀ i, Nat.card (bad i) ≤ K i)
    {a b : ℝ} (hab : a ≤ b) :
    ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
      C.card ≤ 2 + ∑ i, K i ∧
      ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
        ∀ i, ∀ x ∈ Ioo u v, x ∉ bad i := by
  classical
  let F : Finset ℝ := Finset.univ.biUnion (fun i => (hfin i).toFinset)
  let D : Finset ℝ := F.filter (fun x => x ∈ Icc a b)
  let C : Finset ℝ := {a,b} ∪ D
  have hC : ∀ c ∈ C, c ∈ Icc a b := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_insert.mp hc with rfl | hc
      · exact ⟨le_rfl,hab⟩
      · have : c = b := Finset.mem_singleton.mp hc
        subst c
        exact ⟨hab,le_rfl⟩
    · exact (Finset.mem_filter.mp hc).2
  have hF : F.card ≤ ∑ i, K i := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro i _
    simpa only [Nat.card_eq_card_finite_toFinset (hfin i)] using hcard i
  refine ⟨C,by simp [C],by simp [C],hC,?_,?_⟩
  · exact (Finset.card_union_le {a,b} D).trans
      (add_le_add Finset.card_le_two ((Finset.card_filter_le F _).trans hF))
  · intro u hu v hv _ hgap i x hx hxi
    apply hgap x
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,(hfin i).mem_toFinset.mpr hxi⟩,
        ⟨(hC u hu).1.trans hx.1.le,hx.2.le.trans (hC v hv).2⟩⟩
    · exact hx

end PaperI
