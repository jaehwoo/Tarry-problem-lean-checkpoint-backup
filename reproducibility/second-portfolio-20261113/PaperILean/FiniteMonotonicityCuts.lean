import PaperILean.LocalMonotonicityPropagation
import Mathlib.SetTheory.Cardinal.Finite

/-! Construct actual cut sets from the finite exceptional locus. This is local
topological work, independent of any semialgebraic or published input. The
result feeds the existing sorted common-refinement construction. -/

noncomputable section
namespace PaperI
open Set

/-- Add the two endpoints to all actual bad points. Degenerate intervals need
only one endpoint and satisfy the same upper bound. -/
theorem exists_monotone_cut_set_of_finite_bad_set
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hfin : (MonotonicityBadSet f a b).Finite) :
    ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
      MonotoneOnCutIntervals f C ∧
      C.card ≤ Nat.card (MonotonicityBadSet f a b) + 2 := by
  classical
  let C := insert a (insert b hfin.toFinset)
  have hC : ∀ c ∈ C, c ∈ Icc a b := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨le_rfl, hab⟩
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨hab, le_rfl⟩
    exact ⟨(hfin.mem_toFinset.mp hc).1.1.le, (hfin.mem_toFinset.mp hc).1.2.le⟩
  refine ⟨C, by simp [C], by simp [C], hC, ?_, ?_⟩
  · intro u hu v hv _ hgap
    apply monotoneOn_or_antitoneOn_of_no_bad_points hf (hC u hu).1 (hC v hv).2
    intro x hx hbad
    exact hgap x (by simp only [C, Finset.mem_insert]; exact Or.inr (Or.inr (hfin.mem_toFinset.mpr hbad))) hx
  · have h₁ := Finset.card_insert_le a (insert b hfin.toFinset)
    have h₂ := Finset.card_insert_le b hfin.toFinset
    rw [Nat.card_eq_card_finite_toFinset hfin]
    change (insert a (insert b hfin.toFinset)).card ≤ hfin.toFinset.card + 2
    omega

end PaperI
