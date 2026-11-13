import PaperILean.CommonMonotonePartition

/-! Retain the strict adjacent-cut information from the same sorted finite union.
Empty coordinate families and degenerate outer intervals remain allowed. -/
noncomputable section
namespace PaperI
open Set
open scoped BigOperators

theorem exists_strict_common_monotone_partition
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (cuts : ι → Finset ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ i, a ∈ cuts i) (hb : ∀ i, b ∈ cuts i)
    (hcuts : ∀ i, ∀ c ∈ cuts i, c ∈ Icc a b)
    (hf : ∀ i, MonotoneOnCutIntervals (f i) (cuts i)) :
    ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ 1 + ∑ i, (cuts i).card ∧
      t 0 = a ∧ t n = b ∧ MonotoneOn t (Icc 0 n) ∧
      ∀ j < n, t j < t (j + 1) ∧ ∀ i, MonotoneOn (f i) (Ioo (t j) (t (j + 1))) ∨
        AntitoneOn (f i) (Ioo (t j) (t (j + 1))) := by
  classical
  let C : Finset ℝ := {a, b} ∪ Finset.univ.biUnion cuts
  have haC : a ∈ C := Finset.mem_union_left _ (by simp)
  have hbC : b ∈ C := Finset.mem_union_left _ (by simp)
  have hsub (i : ι) : cuts i ⊆ C := by
    intro c hc
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hc⟩)
  have hC : ∀ c ∈ C, c ∈ Icc a b := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact ⟨le_rfl, hab⟩
      · exact ⟨hab, le_rfl⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hc
      exact hcuts i c hi
  have hcard : C.card ≤ 2 + ∑ i, (cuts i).card := by
    calc
      C.card ≤ ({a, b} : Finset ℝ).card + (Finset.univ.biUnion cuts).card :=
        Finset.card_union_le _ _
      _ ≤ 2 + ∑ i, (cuts i).card :=
        add_le_add Finset.card_le_two Finset.card_biUnion_le
  obtain ⟨n, t, hn, ht0, htn, ht, hgap⟩ := exists_sorted_cut_partition C haC hbC hC
  refine ⟨n, t, by omega, ht0, htn, ht, ?_⟩
  intro j hj
  obtain ⟨hu, hv, huv, hno⟩ := hgap j hj
  refine ⟨huv, ?_⟩
  intro i
  obtain ⟨l, hl, r, hr, hlu, hvr, hlr, hnone⟩ :=
    exists_consecutive_cuts_containing (cuts i) (ha i) (hb i)
      (hC _ hu).1 (hC _ hv).2 huv (fun c hc => hno c (hsub i hc))
  rcases hf i l hl r hr hlr hnone with hm | hm
  · exact Or.inl (hm.mono (Set.Ioo_subset_Ioo hlu hvr))
  · exact Or.inr (hm.mono (Set.Ioo_subset_Ioo hlu hvr))

theorem exists_strict_common_partition_of_individual_subdivisions
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (K : ι → ℕ)
    {a b : ℝ} (hab : a ≤ b)
    (hindividual : ∀ i, ∃ C : Finset ℝ,
      a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
      MonotoneOnCutIntervals (f i) C ∧ C.card ≤ K i) :
    ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ 1 + ∑ i, K i ∧
      t 0 = a ∧ t n = b ∧ MonotoneOn t (Icc 0 n) ∧
      ∀ j < n, t j < t (j + 1) ∧ ∀ i,
        MonotoneOn (f i) (Ioo (t j) (t (j + 1))) ∨
        AntitoneOn (f i) (Ioo (t j) (t (j + 1))) := by
  classical
  choose cuts ha hb hcuts hf hcard using hindividual
  obtain ⟨n, t, hn, hrest⟩ :=
    exists_strict_common_monotone_partition f cuts hab ha hb hcuts hf
  exact ⟨n, t, hn.trans (Nat.add_le_add_left (Finset.sum_le_sum (fun i _ => hcard i)) 1), hrest⟩

end PaperI

