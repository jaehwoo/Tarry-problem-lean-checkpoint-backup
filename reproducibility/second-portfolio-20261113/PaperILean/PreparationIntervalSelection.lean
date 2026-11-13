import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Finite interval bookkeeping in the original preparation argument.
These lemmas do not construct derivative good sets or assume semialgebraic
preparation. Their interval families and quantitative bounds are explicit
inputs. Overlap, empty intervals, and singleton endpoints are allowed. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace PaperI

/-- Positive total mass and an upper bound on the number of terms retain one
term of size at least mass divided by that bound. -/
theorem preparation_exists_large_member {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) {M : ℝ} (hM : 0 < M) {K : ℕ} (hK : 0 < K)
    (hcard : s.card ≤ K) (hsum : M ≤ ∑ i ∈ s, w i) :
    ∃ i ∈ s, M / (K : ℝ) ≤ w i := by
  have hs : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.sum_empty] at hsum
    exact (not_le_of_gt hM) hsum
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  apply Finset.exists_le_of_sum_le hs
  calc
    ∑ _i ∈ s, M / (K : ℝ) = (s.card : ℝ) * (M / (K : ℝ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K : ℝ) * (M / (K : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt (div_pos hM hKr))
    _ = M := mul_div_cancel₀ M (ne_of_gt hKr)
    _ ≤ ∑ i ∈ s, w i := hsum

/-- A finite union of intervals has at most the sum of their nonnegative
lengths. No disjointness or ordering of each pair of endpoints is needed. -/
theorem preparation_interval_union_volume_le {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) :
    volume.real (⋃ i ∈ s, Ioo (a i) (b i)) ≤
      ∑ i ∈ s, max (b i - a i) 0 := by
  simpa only [Real.volume_real_Ioo] using
    (measureReal_biUnion_finset_le (μ := volume) s (fun i => Ioo (a i) (b i)))

/-- Summing finite exceptional-set budgets does not require disjointness or
measurability of the individual exceptional sets. -/
theorem preparation_finite_exceptional_union_le {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (E : ι → Set α) (budget : ι → ℝ)
    (hbudget : ∀ i ∈ s, 0 ≤ budget i)
    (hE : ∀ i ∈ s, μ (E i) ≤ ENNReal.ofReal (budget i)) :
    μ (⋃ i ∈ s, E i) ≤ ENNReal.ofReal (∑ i ∈ s, budget i) := by
  calc
    μ (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, μ (E i) := measure_biUnion_finset_le s E
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (budget i) := Finset.sum_le_sum hE
    _ = ENNReal.ofReal (∑ i ∈ s, budget i) :=
      (ENNReal.ofReal_sum_of_nonneg hbudget).symm

/-- At most K intervals of length at most c have union measure at most Kc.
Reversed and degenerate intervals are harmless, since c is nonnegative. -/
theorem preparation_short_interval_union_le {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) {K : ℕ} (hcard : s.card ≤ K)
    (hlen : ∀ i ∈ s, b i - a i ≤ c) :
    volume (⋃ i ∈ s, Ioo (a i) (b i)) ≤ ENNReal.ofReal ((K : ℝ) * c) := by
  have hlength : ∀ i ∈ s, volume (Ioo (a i) (b i)) ≤ ENNReal.ofReal c := by
    intro i hi
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_le_ofReal (hlen i hi)
  calc
    volume (⋃ i ∈ s, Ioo (a i) (b i)) ≤
        ENNReal.ofReal (∑ _i ∈ s, c) :=
      preparation_finite_exceptional_union_le volume s _ (fun _ => c)
        (fun _ _ => hc) hlength
    _ = ENNReal.ofReal ((s.card : ℝ) * c) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((K : ℝ) * c) := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc)

theorem preparation_short_interval_union_real_le {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) {K : ℕ} (hcard : s.card ≤ K)
    (hlen : ∀ i ∈ s, b i - a i ≤ c) :
    volume.real (⋃ i ∈ s, Ioo (a i) (b i)) ≤ (K : ℝ) * c := by
  calc
    volume.real (⋃ i ∈ s, Ioo (a i) (b i)) ≤
        ∑ i ∈ s, max (b i - a i) 0 := preparation_interval_union_volume_le s a b
    _ ≤ ∑ _i ∈ s, c := Finset.sum_le_sum (fun i hi => max_le (hlen i hi) hc)
    _ = (s.card : ℝ) * c := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K : ℝ) * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc

/-- Discarding the members shorter than c costs at most Kc in measure. -/
theorem preparation_discard_short_intervals_le {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) {K : ℕ} (hcard : s.card ≤ K) :
    volume (⋃ i ∈ s, ⋃ (_ : b i - a i < c), Ioo (a i) (b i)) ≤
      ENNReal.ofReal ((K : ℝ) * c) := by
  classical
  have h := preparation_short_interval_union_le (s.filter (fun i => b i - a i < c))
    a b hc ((Finset.card_filter_le s _).trans hcard)
    (fun i hi => (Finset.mem_filter.mp hi).2.le)
  simpa only [Finset.mem_filter, iUnion_and] using h

/-- Intersect finitely many good conditions, retaining the exact pointwise
predicates and the sum of their exceptional budgets. -/
theorem preparation_common_good_set {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (D : Set α) (s : Finset ι) (E : ι → Set α)
    (P : ι → α → Prop) (budget : ι → ℝ)
    (hbudget : ∀ i ∈ s, 0 ≤ budget i)
    (hE : ∀ i ∈ s, μ (E i) ≤ ENNReal.ofReal (budget i))
    (hP : ∀ i ∈ s, ∀ x ∈ D, x ∉ E i → P i x) :
    ∃ G : Set α, G ⊆ D ∧
      μ (D \ G) ≤ ENNReal.ofReal (∑ i ∈ s, budget i) ∧
      ∀ x ∈ G, ∀ i ∈ s, P i x := by
  refine ⟨D \ ⋃ i ∈ s, E i, diff_subset, ?_, ?_⟩
  · apply (measure_mono ?_).trans
      (preparation_finite_exceptional_union_le μ s E budget hbudget hE)
    intro x hx
    by_contra h
    exact hx.2 ⟨hx.1, h⟩
  · intro x hx i hi
    apply hP i hi x hx.1
    intro hxi
    exact hx.2 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxi⟩⟩)

/-- The common good set can be chosen measurable when the domain and all
exceptional sets are measurable, as needed in the subsequent Fubini step. -/
theorem preparation_common_measurable_good_set {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (D : Set α) (hD : MeasurableSet D) (s : Finset ι)
    (E : ι → Set α) (hEm : ∀ i ∈ s, MeasurableSet (E i))
    (P : ι → α → Prop) (budget : ι → ℝ)
    (hbudget : ∀ i ∈ s, 0 ≤ budget i)
    (hE : ∀ i ∈ s, μ (E i) ≤ ENNReal.ofReal (budget i))
    (hP : ∀ i ∈ s, ∀ x ∈ D, x ∉ E i → P i x) :
    ∃ G : Set α, MeasurableSet G ∧ G ⊆ D ∧
      μ (D \ G) ≤ ENNReal.ofReal (∑ i ∈ s, budget i) ∧
      ∀ x ∈ G, ∀ i ∈ s, P i x := by
  refine ⟨D \ ⋃ i ∈ s, E i, hD.diff (s.measurableSet_biUnion hEm), diff_subset, ?_, ?_⟩
  · apply (measure_mono ?_).trans
      (preparation_finite_exceptional_union_le μ s E budget hbudget hE)
    intro x hx
    by_contra h
    exact hx.2 ⟨hx.1, h⟩
  · intro x hx i hi
    apply hP i hi x hx.1
    intro hxi
    exact hx.2 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxi⟩⟩)

/-- Positive measure in a union of at most K open intervals retains an actual
member, with the same original index, whose length is at least M/K. -/
theorem preparation_exists_long_interval {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) {M : ℝ} (hM : 0 < M) {K : ℕ} (hK : 0 < K)
    (hcard : s.card ≤ K)
    (hmass : M ≤ volume.real (⋃ i ∈ s, Ioo (a i) (b i))) :
    ∃ i ∈ s, a i < b i ∧ M / (K : ℝ) ≤ b i - a i := by
  obtain ⟨i, hi, hlarge⟩ := preparation_exists_large_member s
    (fun i => max (b i - a i) 0) hM hK hcard
    (hmass.trans (preparation_interval_union_volume_le s a b))
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hpos : 0 < max (b i - a i) 0 := (div_pos hM hKr).trans_le hlarge
  have hab : a i < b i := by
    by_contra h
    have hba : b i - a i ≤ 0 := sub_nonpos.mpr (le_of_not_gt h)
    rw [max_eq_right hba] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨i, hi, hab, ?_⟩
  simpa only [max_eq_left (sub_nonneg.mpr hab.le)] using hlarge

/-- The central closed half of an open interval stays in the open interval.
This explicit shrink prevents an unwarranted claim at good-set endpoints. -/
theorem preparation_closed_middle_half {a b : ℝ} (hab : a < b) :
    Icc ((3 * a + b) / 4) ((a + 3 * b) / 4) ⊆ Ioo a b ∧
      (a + 3 * b) / 4 - (3 * a + b) / 4 = (b - a) / 2 := by
  constructor
  · intro x hx
    constructor <;> linarith [hx.1, hx.2]
  · ring

/-- The selected interval retains any pointwise property already established
on the good intervals. The closed subinterval has half the length. -/
theorem preparation_retained_closed_interval {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) (P : ℝ → Prop) {M : ℝ} (hM : 0 < M)
    {K : ℕ} (hK : 0 < K) (hcard : s.card ≤ K)
    (hmass : M ≤ volume.real (⋃ i ∈ s, Ioo (a i) (b i)))
    (hP : ∀ i ∈ s, ∀ x ∈ Ioo (a i) (b i), P x) :
    ∃ i ∈ s, ∃ u v : ℝ, u < v ∧ Icc u v ⊆ Ioo (a i) (b i) ∧
      M / (2 * (K : ℝ)) ≤ v - u ∧ ∀ x ∈ Icc u v, P x := by
  obtain ⟨i, hi, hab, hlen⟩ := preparation_exists_long_interval s a b hM hK hcard hmass
  obtain ⟨hsub, hdiff⟩ := preparation_closed_middle_half hab
  refine ⟨i, hi, (3 * a i + b i) / 4, (a i + 3 * b i) / 4,
    by linarith, hsub, ?_, fun x hx => hP i hi x (hsub hx)⟩
  rw [hdiff]
  calc
    M / (2 * (K : ℝ)) = (M / (K : ℝ)) / 2 := by ring
    _ ≤ (b i - a i) / 2 := div_le_div_of_nonneg_right hlen (by norm_num)

/-- An exceptional-length estimate in an ambient interval gives the measure
input needed to retain a long good interval. -/
theorem preparation_good_interval_mass {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) {A B ε : ℝ} (hAB : A ≤ B)
    (hsub : (⋃ i ∈ s, Ioo (a i) (b i)) ⊆ Icc A B)
    (hbad : volume.real (Icc A B \ ⋃ i ∈ s, Ioo (a i) (b i)) ≤ ε * (B - A)) :
    (1 - ε) * (B - A) ≤ volume.real (⋃ i ∈ s, Ioo (a i) (b i)) := by
  have hm : MeasurableSet (⋃ i ∈ s, Ioo (a i) (b i)) :=
    s.measurableSet_biUnion (fun _ _ => measurableSet_Ioo)
  rw [measureReal_diff hsub hm (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top),
    Real.volume_real_Icc_of_le hAB] at hbad
  linarith

/-- The comparable-length interval step used after preparation, including the
same original interval index and all pointwise good conditions. -/
theorem preparation_retained_interval_of_small_exceptional_set {ι : Type*}
    (s : Finset ι) (a b : ι → ℝ) (P : ℝ → Prop) {A B ε : ℝ}
    (hAB : A < B) (hε : ε < 1) {K : ℕ} (hK : 0 < K)
    (hcard : s.card ≤ K) (hsub : (⋃ i ∈ s, Ioo (a i) (b i)) ⊆ Icc A B)
    (hbad : volume.real (Icc A B \ ⋃ i ∈ s, Ioo (a i) (b i)) ≤ ε * (B - A))
    (hP : ∀ i ∈ s, ∀ x ∈ Ioo (a i) (b i), P x) :
    ∃ i ∈ s, ∃ u v : ℝ, u < v ∧ Icc u v ⊆ Ioo (a i) (b i) ∧
      (1 - ε) * (B - A) / (2 * (K : ℝ)) ≤ v - u ∧
      ∀ x ∈ Icc u v, P x := by
  apply preparation_retained_closed_interval s a b P
    (mul_pos (sub_pos.mpr hε) (sub_pos.mpr hAB)) hK hcard
    (preparation_good_interval_mass s a b hAB.le hsub hbad) hP

end PaperI
