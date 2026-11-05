import PaperILean.FiniteMonotoneVariation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

/-! A common monotone subdivision is constructed by sorting the union of individual
finite cut sets. The individual cuts and their monotonicity are inputs. This does
not construct a semialgebraic path or prove a quantitative one-function subdivision. -/

noncomputable section

namespace PaperI
open Set
open scoped BigOperators

/-- Monotonicity on every consecutive open interval in a finite cut set. -/
def MonotoneOnCutIntervals (f : ℝ → ℝ) (C : Finset ℝ) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
    MonotoneOn f (Ioo u v) ∨ AntitoneOn f (Ioo u v)

/-- An interval without an original cut lies inside one original consecutive interval. -/
theorem exists_consecutive_cuts_containing (C : Finset ℝ) {a b u v : ℝ}
    (ha : a ∈ C) (hb : b ∈ C) (hau : a ≤ u) (hvb : v ≤ b) (huv : u < v)
    (hgap : ∀ c ∈ C, c ∉ Ioo u v) :
    ∃ l ∈ C, ∃ r ∈ C, l ≤ u ∧ v ≤ r ∧ l < r ∧ ∀ c ∈ C, c ∉ Ioo l r := by
  classical
  let L := C.filter (fun c => c ≤ u)
  let R := C.filter (fun c => v ≤ c)
  have hL : L.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, hau⟩⟩
  have hR : R.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hvb⟩⟩
  let l := L.max' hL
  let r := R.min' hR
  have hl : l ∈ C ∧ l ≤ u := Finset.mem_filter.mp (L.max'_mem hL)
  have hr : r ∈ C ∧ v ≤ r := Finset.mem_filter.mp (R.min'_mem hR)
  refine ⟨l, hl.1, r, hr.1, hl.2, hr.2, hl.2.trans_lt (huv.trans_le hr.2), ?_⟩
  intro c hc hcr
  by_cases hcu : c ≤ u
  · have hcl : c ≤ l := L.le_max' c (Finset.mem_filter.mpr ⟨hc, hcu⟩)
    exact (not_lt_of_ge hcl) hcr.1
  · have huc : u < c := lt_of_not_ge hcu
    have hvc : v ≤ c := by
      by_contra h
      exact hgap c hc ⟨huc, lt_of_not_ge h⟩
    have hrc : r ≤ c := R.min'_le c (Finset.mem_filter.mpr ⟨hc, hvc⟩)
    exact (not_lt_of_ge hrc) hcr.2

/-- Sorting a finite cut set yields an actual adjacent partition. It extends
constantly after its last index; no additional partition pieces are introduced. -/
theorem exists_sorted_cut_partition (C : Finset ℝ) {a b : ℝ}
    (ha : a ∈ C) (hb : b ∈ C) (hC : ∀ c ∈ C, c ∈ Icc a b) :
    ∃ (n : ℕ) (t : ℕ → ℝ), n + 1 = C.card ∧ t 0 = a ∧ t n = b ∧
      MonotoneOn t (Icc 0 n) ∧
      ∀ j < n, t j ∈ C ∧ t (j + 1) ∈ C ∧ t j < t (j + 1) ∧
        ∀ c ∈ C, c ∉ Ioo (t j) (t (j + 1)) := by
  classical
  have hpos : 0 < C.card := Finset.card_pos.mpr ⟨a, ha⟩
  let n := C.card - 1
  have hn : n + 1 = C.card := Nat.sub_add_cancel hpos
  have hnlt : n < C.card := by omega
  let e : Fin C.card ↪o ℝ := C.orderEmbOfFin rfl
  let t : ℕ → ℝ := fun k => e ⟨min k n, lt_of_le_of_lt (min_le_right k n) hnlt⟩
  have ht (k : ℕ) (hk : k ≤ n) : t k = e ⟨k, hk.trans_lt hnlt⟩ := by
    simp only [t, min_eq_left hk]
  have he_mem (k : Fin C.card) : e k ∈ C := C.orderEmbOfFin_mem rfl k
  have he_surj (c : ℝ) (hc : c ∈ C) : ∃ k : Fin C.card, e k = c := by
    have hc' : c ∈ Set.range (C.orderEmbOfFin rfl) := by
      rw [C.range_orderEmbOfFin rfl]
      exact hc
    exact hc'
  have ht0 : t 0 = a := by
    rw [ht 0 (Nat.zero_le _)]
    apply le_antisymm
    · obtain ⟨k, hk⟩ := he_surj a ha
      rw [← hk]
      apply e.monotone
      change (0 : ℕ) ≤ k.val
      exact Nat.zero_le _
    · exact (hC _ (he_mem _)).1
  have htn : t n = b := by
    rw [ht n le_rfl]
    apply le_antisymm
    · exact (hC _ (he_mem _)).2
    · obtain ⟨k, hk⟩ := he_surj b hb
      rw [← hk]
      apply e.monotone
      change k.val ≤ n
      have := k.isLt
      omega
  have hmono : MonotoneOn t (Icc 0 n) := by
    intro i hi j hj hij
    rw [ht i hi.2, ht j hj.2]
    exact e.monotone hij
  refine ⟨n, t, hn, ht0, htn, hmono, ?_⟩
  intro j hj
  have hjs : j + 1 ≤ n := hj
  rw [ht j hj.le, ht (j + 1) hjs]
  refine ⟨he_mem _, he_mem _, e.strictMono (Nat.lt_succ_self j), ?_⟩
  intro c hc hbetween
  obtain ⟨k, hk⟩ := he_surj c hc
  rw [← hk] at hbetween
  have hleft : j < k.val := by
    apply Nat.lt_of_not_ge
    intro hkj
    exact (not_lt_of_ge (e.monotone hkj)) hbetween.1
  have hright : k.val < j + 1 := by
    apply Nat.lt_of_not_ge
    intro hjk
    exact (not_lt_of_ge (e.monotone hjk)) hbetween.2
  omega

/-- The sorted union refines every individual finite partition. The bound retains
its dependence on the number and sizes of the individual cut sets. -/
theorem exists_common_monotone_partition
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (cuts : ι → Finset ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ i, a ∈ cuts i) (hb : ∀ i, b ∈ cuts i)
    (hcuts : ∀ i, ∀ c ∈ cuts i, c ∈ Icc a b)
    (hf : ∀ i, MonotoneOnCutIntervals (f i) (cuts i)) :
    ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ 1 + ∑ i, (cuts i).card ∧
      t 0 = a ∧ t n = b ∧ MonotoneOn t (Icc 0 n) ∧
      ∀ j < n, ∀ i, MonotoneOn (f i) (Ioo (t j) (t (j + 1))) ∨
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
  intro j hj i
  obtain ⟨hu, hv, huv, hno⟩ := hgap j hj
  obtain ⟨l, hl, r, hr, hlu, hvr, hlr, hnone⟩ :=
    exists_consecutive_cuts_containing (cuts i) (ha i) (hb i)
      (hC _ hu).1 (hC _ hv).2 huv (fun c hc => hno c (hsub i hc))
  rcases hf i l hl r hr hlr hnone with hm | hm
  · exact Or.inl (hm.mono (Set.Ioo_subset_Ioo hlu hvr))
  · exact Or.inr (hm.mono (Set.Ioo_subset_Ioo hlu hvr))

/-- Prescribed individual cut-count bounds give a common bound before the function
index; no independence from the number of functions is asserted. -/
theorem exists_common_monotone_partition_of_card_bounds
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (cuts : ι → Finset ℝ) (K : ι → ℕ)
    {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ i, a ∈ cuts i) (hb : ∀ i, b ∈ cuts i)
    (hcuts : ∀ i, ∀ c ∈ cuts i, c ∈ Icc a b)
    (hf : ∀ i, MonotoneOnCutIntervals (f i) (cuts i))
    (hcard : ∀ i, (cuts i).card ≤ K i) :
    ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ 1 + ∑ i, K i ∧
      t 0 = a ∧ t n = b ∧ MonotoneOn t (Icc 0 n) ∧
      ∀ j < n, ∀ i, MonotoneOn (f i) (Ioo (t j) (t (j + 1))) ∨
        AntitoneOn (f i) (Ioo (t j) (t (j + 1))) := by
  obtain ⟨n, t, hn, hrest⟩ := exists_common_monotone_partition f cuts hab ha hb hcuts hf
  exact ⟨n, t, hn.trans (Nat.add_le_add_left (Finset.sum_le_sum (fun i _ => hcard i)) 1), hrest⟩

/-- Combining the constructed common partition with the checked variation estimate.
Continuity includes endpoints; individual monotonicity is only needed on open cells. -/
theorem family_variation_le_of_individual_cut_sets
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (cuts : ι → Finset ℝ)
    (K : ι → ℕ) (B : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ i, a ∈ cuts i) (hb : ∀ i, b ∈ cuts i)
    (hcuts : ∀ i, ∀ c ∈ cuts i, c ∈ Icc a b)
    (hf : ∀ i, MonotoneOnCutIntervals (f i) (cuts i))
    (hcard : ∀ i, (cuts i).card ≤ K i)
    (hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (hB : ∀ i, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f i x - f i y| ≤ B i) :
    ∀ i, BoundedVariationOn (f i) (Icc a b) ∧
      variationOnFromTo (f i) Set.univ a b ≤ ((1 + ∑ k, K k : ℕ) : ℝ) * B i := by
  obtain ⟨n, t, hn, ht0, htn, ht, hm⟩ :=
    exists_common_monotone_partition_of_card_bounds f cuts K hab ha hb hcuts hf hcard
  have hvar := family_variation_le_of_bounded_common_partition f B (1 + ∑ k, K k)
    t n hn ht (by simpa only [ht0, htn] using hc) hm
    (by simpa only [ht0, htn] using hB)
  simpa only [ht0, htn] using hvar

/-- Individual subdivision existence yields one simultaneous partition. The
individual cut bounds are fixed before choosing any cuts. -/
theorem exists_common_partition_of_individual_subdivisions
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (K : ι → ℕ)
    {a b : ℝ} (hab : a ≤ b)
    (hindividual : ∀ i, ∃ C : Finset ℝ,
      a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
      MonotoneOnCutIntervals (f i) C ∧ C.card ≤ K i) :
    ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ 1 + ∑ i, K i ∧
      t 0 = a ∧ t n = b ∧ MonotoneOn t (Icc 0 n) ∧
      ∀ j < n, ∀ i, MonotoneOn (f i) (Ioo (t j) (t (j + 1))) ∨
        AntitoneOn (f i) (Ioo (t j) (t (j + 1))) := by
  classical
  choose cuts ha hb hcuts hf hcard using hindividual
  exact exists_common_monotone_partition_of_card_bounds f cuts K hab ha hb hcuts hf hcard

end PaperI
