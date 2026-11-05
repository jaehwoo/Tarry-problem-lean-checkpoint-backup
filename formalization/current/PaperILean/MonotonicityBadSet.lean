import PaperILean.CommonMonotonePartition

/-! The exceptional locus for strict one-variable monotonicity. Weak local
monotone-or-antitone is insufficient: a constant plateau permits a direction
change. The three local alternatives below exclude such unrecorded transitions. -/

noncomputable section
namespace PaperI
open Set

/-- A genuine open neighborhood inside `(a,b)` is strictly increasing, strictly
decreasing, or constant. The graph need not be specified outside `[a,b]`. -/
def LocalStrictMonotoneOrConstant (f : ℝ → ℝ) (a b x : ℝ) : Prop :=
  ∃ u v : ℝ, a ≤ u ∧ v ≤ b ∧ u < x ∧ x < v ∧
    (StrictMonoOn f (Ioo u v) ∨ StrictAntiOn f (Ioo u v) ∨
      ∀ s ∈ Ioo u v, f s = f x)

/-- Interior points without any of the three genuine local monotonicity types. -/
def MonotonicityBadSet (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {x | x ∈ Ioo a b ∧ ¬ LocalStrictMonotoneOrConstant f a b x}

theorem localStrictMonotoneOrConstant_mem_Ioo {f : ℝ → ℝ} {a b x : ℝ}
    (h : LocalStrictMonotoneOrConstant f a b x) : x ∈ Ioo a b := by
  obtain ⟨u, v, hau, hvb, hux, hxv, _⟩ := h
  exact ⟨hau.trans_lt hux, hxv.trans_le hvb⟩

theorem monotonicityBadSet_subset_Ioo (f : ℝ → ℝ) (a b : ℝ) :
    MonotonicityBadSet f a b ⊆ Ioo a b := fun _ hx => hx.1

theorem not_mem_monotonicityBadSet_iff {f : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Ioo a b) :
    x ∉ MonotonicityBadSet f a b ↔ LocalStrictMonotoneOrConstant f a b x := by
  classical
  simp only [MonotonicityBadSet, Set.mem_setOf_eq, hx, true_and, not_not]

end PaperI
