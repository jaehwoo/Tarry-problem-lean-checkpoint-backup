import PaperILean.CommonMonotonePartition

set_option pp.proofs false

#print PaperI.MonotoneOnCutIntervals
#print axioms PaperI.MonotoneOnCutIntervals

#print PaperI.exists_consecutive_cuts_containing
#print axioms PaperI.exists_consecutive_cuts_containing

#print PaperI.exists_sorted_cut_partition
#print axioms PaperI.exists_sorted_cut_partition

#print PaperI.exists_common_monotone_partition
#print axioms PaperI.exists_common_monotone_partition

#print PaperI.exists_common_monotone_partition_of_card_bounds
#print axioms PaperI.exists_common_monotone_partition_of_card_bounds

#print PaperI.family_variation_le_of_individual_cut_sets
#print axioms PaperI.family_variation_le_of_individual_cut_sets

#print PaperI.exists_common_partition_of_individual_subdivisions
#print axioms PaperI.exists_common_partition_of_individual_subdivisions

-- Equal endpoints sort to one cut, hence zero partition intervals.
example (a : ℝ) : ∃ t : ℕ → ℝ, t 0 = a ∧ MonotoneOn t (Set.Icc 0 0) := by
  obtain ⟨n, t, hn, h0, hlast, ht, hgap⟩ :=
    PaperI.exists_sorted_cut_partition {a} (Finset.mem_singleton_self a)
      (Finset.mem_singleton_self a) (by intro c hc; simpa using hc)
  have hn0 : n = 0 := by simpa using hn
  subst n
  exact ⟨t, h0, ht⟩

-- There may be no functions: the endpoint partition still exists without choosing an index.
example {a b : ℝ} (hab : a ≤ b) :
    ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ 1 ∧ t 0 = a ∧ t n = b ∧
      MonotoneOn t (Set.Icc 0 n) := by
  obtain ⟨n, t, hn, h0, hlast, ht, _⟩ :=
    PaperI.exists_common_monotone_partition
      (fun i : Empty => Empty.elim i) (fun i : Empty => Empty.elim i)
      hab (fun i => Empty.elim i) (fun i => Empty.elim i)
      (fun i => Empty.elim i) (fun i => Empty.elim i)
  exact ⟨n, t, by simpa using hn, h0, hlast, ht⟩

-- Constant functions allow arbitrary finite cut sets, including repeated endpoints after deduplication.
example (c : ℝ) (C : Finset ℝ) : PaperI.MonotoneOnCutIntervals (fun _ => c) C := by
  intro u hu v hv huv hgap
  exact Or.inl (monotone_const.monotoneOn _)
