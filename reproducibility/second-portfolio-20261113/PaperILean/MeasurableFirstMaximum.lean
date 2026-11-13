import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.Nat.Find

/-! I1265 fixed ties: the FIRST maximum in a finite prefix is measurable,
even when the positive prefix length varies measurably. This does not supply
the still missing joint cut/direction data to which it will be applied. -/
noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable

def PrefixMaximum (f : ℕ → ℝ) (n k : ℕ) : Prop :=
  k < n ∧ ∀ j < n, f j ≤ f k

theorem exists_prefixMaximum (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ k, PrefixMaximum f n k := by
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.range n) f ⟨0,by simp [hn]⟩
  exact ⟨j,Finset.mem_range.mp hj,fun k hk => hmax k (Finset.mem_range.mpr hk)⟩

def firstPrefixMaximum (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) : ℕ :=
  Nat.find (exists_prefixMaximum f hn)

theorem firstPrefixMaximum_spec (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    PrefixMaximum f n (firstPrefixMaximum f hn) :=
  Nat.find_spec (exists_prefixMaximum f hn)

theorem firstPrefixMaximum_first (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {j : ℕ} (hj : PrefixMaximum f n j) : firstPrefixMaximum f hn ≤ j :=
  Nat.find_min' (exists_prefixMaximum f hn) hj

theorem firstPrefixMaximum_strict_before (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {j : ℕ} (hj : j < firstPrefixMaximum f hn) :
    f j < f (firstPrefixMaximum f hn) := by
  have hs := firstPrefixMaximum_spec f hn
  have hjn : j < n := hj.trans hs.1
  refine lt_of_le_of_ne (hs.2 j hjn) ?_
  intro he
  have hm : PrefixMaximum f n j := ⟨hjn,fun k hk => by rw [he]; exact hs.2 k hk⟩
  exact (not_lt_of_ge (firstPrefixMaximum_first f hn hm)) hj

theorem measurableSet_prefixMaximum {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℕ → ℝ) (n : Ω → ℕ)
    (hf : ∀ j, Measurable (fun ω => f ω j)) (hn : Measurable n) (k : ℕ) :
    MeasurableSet {ω | PrefixMaximum (f ω) (n ω) k} := by
  have hk : MeasurableSet {ω | k < n ω} := measurableSet_lt measurable_const hn
  have hj : ∀ j, MeasurableSet {ω | j < n ω → f ω j ≤ f ω k} := by
    intro j
    have h := (measurableSet_lt (measurable_const (a := j)) hn).compl.union
      (measurableSet_le (hf j) (hf k))
    convert h using 1
    ext ω
    simp only [mem_union,mem_compl_iff,mem_setOf_eq]
    tauto
  simpa only [PrefixMaximum,setOf_and,setOf_forall] using
    hk.inter (MeasurableSet.iInter hj)

theorem measurable_firstPrefixMaximum {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℕ → ℝ) (n : Ω → ℕ)
    (hf : ∀ j, Measurable (fun ω => f ω j)) (hn : Measurable n)
    (hpos : ∀ ω, 0 < n ω) :
    Measurable (fun ω => firstPrefixMaximum (f ω) (hpos ω)) :=
  measurable_find (fun ω => exists_prefixMaximum (f ω) (hpos ω))
    (measurableSet_prefixMaximum f n hf hn)

theorem measurable_firstPrefixMaximum_data {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (f : Ω → ℕ → ℝ) (n : Ω → ℕ)
    (hf : ∀ j, Measurable (fun ω => f ω j)) (hn : Measurable n)
    (hpos : ∀ ω, 0 < n ω) (data : ℕ → Ω → β)
    (hdata : ∀ j, Measurable (data j)) :
    Measurable (fun ω => data (firstPrefixMaximum (f ω) (hpos ω)) ω) := by
  have hm : Measurable (fun v : Ω × ℕ => data v.2 v.1) :=
    measurable_from_prod_countable hdata
  exact hm.comp (measurable_id.prodMk (measurable_firstPrefixMaximum f n hf hn hpos))

end PaperI
