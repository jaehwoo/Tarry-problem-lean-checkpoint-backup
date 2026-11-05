import PaperILean.FiniteMonotoneVariation

set_option pp.proofs false

#print PaperI.eVariationOn_neg_real
#print axioms PaperI.eVariationOn_neg_real

#print PaperI.eVariationOn_Icc_le_of_monotone_or_antitone
#print axioms PaperI.eVariationOn_Icc_le_of_monotone_or_antitone

#print PaperI.eVariationOn_Icc_le_of_monotone_range
#print axioms PaperI.eVariationOn_Icc_le_of_monotone_range

#print PaperI.eVariationOn_Icc_eq_sum_adjacent
#print axioms PaperI.eVariationOn_Icc_eq_sum_adjacent

#print PaperI.eVariationOn_le_of_finite_monotone_partition
#print axioms PaperI.eVariationOn_le_of_finite_monotone_partition

#print PaperI.boundedVariationOn_of_finite_monotone_partition
#print axioms PaperI.boundedVariationOn_of_finite_monotone_partition

#print PaperI.real_variation_le_of_finite_monotone_partition
#print axioms PaperI.real_variation_le_of_finite_monotone_partition

#print PaperI.family_variation_le_of_common_monotone_partition
#print axioms PaperI.family_variation_le_of_common_monotone_partition

#print PaperI.monotoneOn_Icc_of_continuousOn_Ioo
#print axioms PaperI.monotoneOn_Icc_of_continuousOn_Ioo

#print PaperI.monotone_or_antitone_Icc_of_continuousOn_Ioo
#print axioms PaperI.monotone_or_antitone_Icc_of_continuousOn_Ioo

#print PaperI.family_variation_le_of_continuous_common_partition
#print axioms PaperI.family_variation_le_of_continuous_common_partition

#print PaperI.family_path_variation_le_of_common_partition
#print axioms PaperI.family_path_variation_le_of_common_partition

#print PaperI.family_variation_le_of_bounded_common_partition
#print axioms PaperI.family_variation_le_of_bounded_common_partition

-- Reversed/empty intervals have zero actual extended variation.
example (f : ℝ → ℝ) {a b : ℝ} (h : b < a) :
    eVariationOn f (Set.Icc a b) = 0 := by
  rw [Set.Icc_eq_empty_of_lt h]
  exact eVariationOn.subsingleton f Set.subsingleton_empty

-- Zero pieces and a degenerate interval are included by exact partition additivity.
example (f : ℝ → ℝ) (a : ℝ) : eVariationOn f (Set.Icc a a) = 0 := by
  simpa using PaperI.eVariationOn_Icc_eq_sum_adjacent f (fun _ => a) 0
    (monotone_const.monotoneOn _)

-- Repeated breakpoints impose no restrictions on endpoint values or local slopes.
example (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    eVariationOn f (Set.Icc a a) =
      ∑ _j ∈ Finset.range n, eVariationOn f (Set.Icc a a) := by
  exact PaperI.eVariationOn_Icc_eq_sum_adjacent f (fun _ => a) n
    (monotone_const.monotoneOn _)

-- Constant functions give variation bound zero on a closed interval.
example (c a b : ℝ) (hab : a ≤ b) :
    eVariationOn (fun _ : ℝ => c) (Set.Icc a b) ≤ ENNReal.ofReal 0 := by
  apply PaperI.eVariationOn_Icc_le_of_monotone_range (fun _ : ℝ => c) hab
    (Or.inl (monotone_const.monotoneOn _)) 0
  intro x hx y hy
  simp
