import PaperILean.FiniteMonotonicityCuts

/-! I1261: open-domain monotonicity cuts. No endpoint continuity is assumed.
The existing strict/constant bad locus, not weak local monotonicity, is retained. -/
noncomputable section
namespace PaperI
open Set

theorem monotoneOn_or_antitoneOn_of_no_bad_points_open {f : ℝ → ℝ} {a b u v : ℝ}
    (hf : ContinuousOn f (Ioo a b)) (hau : a ≤ u) (hvb : v ≤ b)
    (hbad : ∀ x ∈ Ioo u v, x ∉ MonotonicityBadSet f a b) :
    MonotoneOn f (Ioo u v) ∨ AntitoneOn f (Ioo u v) := by
  let U := LocalIntervalLocus (StrictMonoOn f)
  let D := LocalIntervalLocus (StrictAntiOn f)
  let C := LocalIntervalLocus (fun S => ∀ x ∈ S, ∀ y ∈ S, f x = f y)
  have hcover : Ioo u v ⊆ U ∪ (D ∪ C) := by
    intro x hx
    have hab : x ∈ Ioo a b := ⟨hau.trans_lt hx.1, hx.2.trans_le hvb⟩
    obtain ⟨l, r, _, _, hl, hr, hm | hm | hc⟩ :=
      (not_mem_monotonicityBadSet_iff hab).mp (hbad x hx)
    · exact Or.inl ⟨l, r, hl, hr, hm⟩
    · exact Or.inr (Or.inl ⟨l, r, hl, hr, hm⟩)
    · exact Or.inr (Or.inr ⟨l, r, hl, hr, fun y hy z hz => (hc y hy).trans (hc z hz).symm⟩)
  have hUD : Disjoint U D := disjoint_local_strictMono_strictAnti f
  have hUC : Disjoint U C := disjoint_local_strictMono_constant f
  have hDC : Disjoint D C := disjoint_local_strictAnti_constant f
  have hcont : ContinuousOn f (Ioo u v) := hf.mono (fun x hx =>
    ⟨hau.trans_lt hx.1, hx.2.trans_le hvb⟩)
  rcases IsPreconnected.subset_or_subset (isOpen_localIntervalLocus _)
      ((isOpen_localIntervalLocus _).union (isOpen_localIntervalLocus _))
      (disjoint_union_right.mpr ⟨hUD, hUC⟩) hcover isPreconnected_Ioo with hU | hDCover
  · exact Or.inl (monotoneOn_of_local_strictMono hcont hU)
  · rcases IsPreconnected.subset_or_subset (isOpen_localIntervalLocus _)
        (isOpen_localIntervalLocus _) hDC hDCover isPreconnected_Ioo with hD | hC
    · exact Or.inr (antitoneOn_of_local_strictAnti hcont hD)
    · exact Or.inl (fun x hx y hy _ => (eqOn_of_local_constant hC x hx y hy).le)

theorem exists_monotone_cut_set_of_finite_bad_set_open
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Ioo a b))
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
    apply monotoneOn_or_antitoneOn_of_no_bad_points_open hf (hC u hu).1 (hC v hv).2
    intro x hx hbad
    exact hgap x (by simp only [C, Finset.mem_insert]; exact Or.inr (Or.inr (hfin.mem_toFinset.mpr hbad))) hx
  · have h₁ := Finset.card_insert_le a (insert b hfin.toFinset)
    have h₂ := Finset.card_insert_le b hfin.toFinset
    rw [Nat.card_eq_card_finite_toFinset hfin]
    change (insert a (insert b hfin.toFinset)).card ≤ hfin.toFinset.card + 2
    omega

end PaperI

