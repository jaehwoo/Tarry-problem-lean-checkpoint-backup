import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Find

/-! I469-476: selecting the first eligible piece by one fixed natural-number
priority. This does not construct the geometric eligible cover. Original labels
are retained; uncovered labels have no assigned piece. The countable priority
is fixed before coefficients, anchors, weights, and the eligible predicates. -/

noncomputable section
namespace PaperI

/-- The first eligible piece in a fixed natural-number ordering. -/
def FirstEligible {Ω κ ι : Type*} (rank : ι → ℕ)
    (eligible : Ω → κ → ι → Prop) (x : Ω) (j : κ) (i : ι) : Prop :=
  eligible x j i ∧ ∀ t, rank t < rank i → ¬ eligible x j t

theorem firstEligible_eligible {Ω κ ι : Type*} {rank : ι → ℕ}
    {eligible : Ω → κ → ι → Prop} {x : Ω} {j : κ} {i : ι}
    (h : FirstEligible rank eligible x j i) : eligible x j i := h.1

theorem firstEligible_not_earlier {Ω κ ι : Type*} {rank : ι → ℕ}
    {eligible : Ω → κ → ι → Prop} {x : Ω} {j : κ} {i t : ι}
    (h : FirstEligible rank eligible x j i) (ht : rank t < rank i) :
    ¬ eligible x j t := h.2 t ht

theorem firstEligible_rank_minimal {Ω κ ι : Type*} {rank : ι → ℕ}
    {eligible : Ω → κ → ι → Prop} {x : Ω} {j : κ} {i t : ι}
    (h : FirstEligible rank eligible x j i) (ht : eligible x j t) :
    rank i ≤ rank t := Nat.le_of_not_lt fun hlt => h.2 t hlt ht

theorem firstEligible_iff_minimal {Ω κ ι : Type*} {rank : ι → ℕ}
    {eligible : Ω → κ → ι → Prop} {x : Ω} {j : κ} {i : ι} :
    FirstEligible rank eligible x j i ↔
      eligible x j i ∧ ∀ t, eligible x j t → rank i ≤ rank t := by
  constructor
  · intro h
    exact ⟨h.1, fun _ ht => firstEligible_rank_minimal h ht⟩
  · rintro ⟨hi, hmin⟩
    exact ⟨hi, fun t hlt ht => (Nat.not_lt_of_ge (hmin t ht)) hlt⟩

theorem firstEligible_unique {Ω κ ι : Type*} {rank : ι → ℕ}
    (hrank : Function.Injective rank) {eligible : Ω → κ → ι → Prop}
    {x : Ω} {j : κ} {i t : ι}
    (hi : FirstEligible rank eligible x j i)
    (ht : FirstEligible rank eligible x j t) : i = t := by
  apply hrank
  exact Nat.le_antisymm (firstEligible_rank_minimal hi ht.1)
    (firstEligible_rank_minimal ht hi.1)

theorem firstEligible_exists {Ω κ ι : Type*} (rank : ι → ℕ)
    {eligible : Ω → κ → ι → Prop} {x : Ω} {j : κ}
    (h : ∃ i, eligible x j i) : ∃ i, FirstEligible rank eligible x j i := by
  classical
  have hn : ∃ n : ℕ, ∃ i, rank i = n ∧ eligible x j i := by
    obtain ⟨i, hi⟩ := h
    exact ⟨rank i, i, rfl, hi⟩
  obtain ⟨i, hi, he⟩ := Nat.find_spec hn
  refine ⟨i, he, ?_⟩
  intro t ht he'
  exact Nat.find_min hn (hi ▸ ht) ⟨t, rfl, he'⟩

theorem firstEligible_exists_iff {Ω κ ι : Type*} (rank : ι → ℕ)
    (eligible : Ω → κ → ι → Prop) (x : Ω) (j : κ) :
    (∃ i, FirstEligible rank eligible x j i) ↔ ∃ i, eligible x j i := by
  exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.1⟩, firstEligible_exists rank⟩

theorem firstEligible_exists_unique_iff {Ω κ ι : Type*} {rank : ι → ℕ}
    (hrank : Function.Injective rank) (eligible : Ω → κ → ι → Prop)
    (x : Ω) (j : κ) :
    (∃! i, FirstEligible rank eligible x j i) ↔ ∃ i, eligible x j i := by
  constructor
  · rintro ⟨i, hi, _⟩
    exact ⟨i, hi.1⟩
  · intro h
    obtain ⟨i, hi⟩ := firstEligible_exists rank h
    exact ⟨i, hi, fun t ht => firstEligible_unique hrank ht hi⟩

theorem firstEligible_none_iff {Ω κ ι : Type*} (rank : ι → ℕ)
    (eligible : Ω → κ → ι → Prop) (x : Ω) (j : κ) :
    (∀ i, ¬ FirstEligible rank eligible x j i) ↔ ∀ i, ¬ eligible x j i := by
  simpa only [not_exists] using not_congr (firstEligible_exists_iff rank eligible x j)

theorem firstEligible_fiber_subset {Ω κ ι : Type*} (rank : ι → ℕ)
    (eligible : Ω → κ → ι → Prop) (j : κ) (i : ι) :
    {x | FirstEligible rank eligible x j i} ⊆ {x | eligible x j i} :=
  fun _ h => h.1

theorem firstEligible_fibers_disjoint {Ω κ ι : Type*} {rank : ι → ℕ}
    (hrank : Function.Injective rank) (eligible : Ω → κ → ι → Prop)
    (j : κ) {i t : ι} (hit : i ≠ t) :
    Disjoint {x | FirstEligible rank eligible x j i}
      {x | FirstEligible rank eligible x j t} := by
  rw [Set.disjoint_left]
  intro x hi ht
  exact hit (firstEligible_unique hrank hi ht)

theorem firstEligible_label_sets_disjoint {Ω κ ι : Type*} {rank : ι → ℕ}
    (hrank : Function.Injective rank) (eligible : Ω → κ → ι → Prop)
    (x : Ω) {i t : ι} (hit : i ≠ t) :
    Disjoint {j | FirstEligible rank eligible x j i}
      {j | FirstEligible rank eligible x j t} := by
  rw [Set.disjoint_left]
  intro j hi ht
  exact hit (firstEligible_unique hrank hi ht)

theorem firstEligible_iUnion {Ω κ ι : Type*} (rank : ι → ℕ)
    (eligible : Ω → κ → ι → Prop) (j : κ) :
    (⋃ i, {x | FirstEligible rank eligible x j i}) = ⋃ i, {x | eligible x j i} := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, firstEligible_exists_iff]

theorem firstEligible_admissible_iff {Ω κ ι : Type*} {rank : ι → ℕ}
    (hrank : Function.Injective rank) (eligible : Ω → κ → ι → Prop)
    (admissible : Ω → κ → Prop)
    (hcover : ∀ x j, admissible x j ↔ ∃ i, eligible x j i) (x : Ω) (j : κ) :
    (∃! i, FirstEligible rank eligible x j i) ↔ admissible x j := by
  rw [firstEligible_exists_unique_iff hrank, ← hcover x j]

theorem measurableSet_firstEligible {Ω κ ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (rank : ι → ℕ) (eligible : Ω → κ → ι → Prop)
    (heligible : ∀ j i, MeasurableSet {x | eligible x j i}) (j : κ) (i : ι) :
    MeasurableSet {x | FirstEligible rank eligible x j i} := by
  classical
  change MeasurableSet ({x | eligible x j i} ∩ {x | ∀ t, rank t < rank i → ¬ eligible x j t})
  apply (heligible j i).inter
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro t
  apply MeasurableSet.iInter
  intro _
  exact (heligible j t).compl

theorem measurableSet_exists_firstEligible {Ω κ ι : Type*}
    [MeasurableSpace Ω] [Countable ι] (rank : ι → ℕ)
    (eligible : Ω → κ → ι → Prop)
    (heligible : ∀ j i, MeasurableSet {x | eligible x j i}) (j : κ) :
    MeasurableSet {x | ∃ i, FirstEligible rank eligible x j i} := by
  simp only [Set.setOf_exists]
  exact MeasurableSet.iUnion fun i => measurableSet_firstEligible rank eligible heligible j i

/-- This priority depends only on the countable label type, before any phase or weight. -/
def countablePieceRank (ι : Type*) [Countable ι] : ι → ℕ :=
  Classical.choose (exists_injective_nat ι)

theorem countablePieceRank_injective (ι : Type*) [Countable ι] :
    Function.Injective (countablePieceRank ι) :=
  Classical.choose_spec (exists_injective_nat ι)

/-- The fixed ranking is chosen before all coefficient spaces, original label
sets, and eligible cover predicates. -/
theorem exists_fixed_countable_piece_rank (ι : Type*) [Countable ι] :
    ∃ rank : ι → ℕ, Function.Injective rank :=
  ⟨countablePieceRank ι, countablePieceRank_injective ι⟩

theorem countable_measurable_first_assignment {Ω κ ι : Type*}
    [MeasurableSpace Ω] [Countable ι]
    (eligible : Ω → κ → ι → Prop)
    (heligible : ∀ j i, MeasurableSet {x | eligible x j i}) :
    (∀ x j, (∃! i, FirstEligible (countablePieceRank ι) eligible x j i) ↔
      ∃ i, eligible x j i) ∧
    (∀ j i, MeasurableSet {x | FirstEligible (countablePieceRank ι) eligible x j i}) := by
  exact ⟨fun x j => firstEligible_exists_unique_iff (countablePieceRank_injective ι) eligible x j,
    measurableSet_firstEligible (countablePieceRank ι) eligible heligible⟩

end PaperI
