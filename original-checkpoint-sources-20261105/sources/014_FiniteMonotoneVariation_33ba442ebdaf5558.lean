import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Normed.Group.Basic

/-! The final local estimate in I647–654. A finite adjacent closed partition and
monotonicity on its pieces give a total-variation bound. This does not construct
a path, analytic pieces, or a format-uniform bound on the number of pieces. -/

noncomputable section

namespace PaperI

open Set
open scoped BigOperators ENNReal

/-- Negation preserves the actual extended total variation. -/
theorem eVariationOn_neg_real {α : Type*} [LinearOrder α]
    (f : α → ℝ) (S : Set α) :
    eVariationOn (fun x => -f x) S = eVariationOn f S := by
  unfold eVariationOn
  simp only [edist_dist, Real.dist_eq, neg_sub_neg, abs_sub_comm]

/-- On a closed monotone piece, increasing or decreasing, variation is at most
its endpoint distance. Endpoint values are included in the hypothesis. -/
theorem eVariationOn_Icc_le_of_monotone_or_antitone
    {α : Type*} [LinearOrder α] (f : α → ℝ) {a b : α} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal |f b - f a| := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  rcases hf with hm | hm
  · have h := hm.eVariationOn_le ha hb
    simp only [Set.inter_self] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
  · have hn : MonotoneOn (fun x => -f x) (Icc a b) := by
      intro x hx y hy hxy
      exact neg_le_neg (hm hx hy hxy)
    have h := hn.eVariationOn_le ha hb
    simp only [Set.inter_self, eVariationOn_neg_real] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (by
      simpa only [neg_sub_neg, abs_sub_comm] using le_abs_self (f a - f b)))

/-- The endpoint estimate follows from a bound on the whole range diameter. -/
theorem eVariationOn_Icc_le_of_monotone_range
    {α : Type*} [LinearOrder α] (f : α → ℝ) {a b : α} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)) (B : ℝ)
    (hB : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f x - f y| ≤ B) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal B :=
  (eVariationOn_Icc_le_of_monotone_or_antitone f hab hf).trans
    (ENNReal.ofReal_le_ofReal (hB b ⟨hab, le_rfl⟩ a ⟨le_rfl, hab⟩))

/-- Adjacent closed pieces give exact additivity, including repeated breakpoints.
Only the finitely many values `t 0, ..., t n` are constrained or used. -/
theorem eVariationOn_Icc_eq_sum_adjacent
    {α E : Type*} [LinearOrder α] [PseudoEMetricSpace E]
    (f : α → E) (t : ℕ → α) (n : ℕ) (ht : MonotoneOn t (Icc 0 n)) :
    eVariationOn f (Icc (t 0) (t n)) =
      ∑ j ∈ Finset.range n, eVariationOn f (Icc (t j) (t (j + 1))) := by
  induction n with
  | zero =>
      simp only [Set.Icc_self, Finset.range_zero, Finset.sum_empty]
      exact eVariationOn.subsingleton f (Set.subsingleton_singleton)
  | succ n ih =>
      have hprev : MonotoneOn t (Icc 0 n) :=
        ht.mono (Set.Icc_subset_Icc le_rfl (Nat.le_succ n))
      have h0n : t 0 ≤ t n := ht ⟨le_rfl, Nat.zero_le _⟩
        ⟨Nat.zero_le _, Nat.le_succ n⟩ (Nat.zero_le n)
      have hnn : t n ≤ t (n + 1) := ht ⟨Nat.zero_le _, Nat.le_succ n⟩
        ⟨Nat.zero_le _, le_rfl⟩ (Nat.le_succ n)
      rw [Finset.sum_range_succ, ← ih hprev]
      simpa only [Set.univ_inter] using
        (eVariationOn.Icc_add_Icc f (s := Set.univ) h0n hnn (Set.mem_univ _)).symm

/-- A partition with `n` monotone pieces gives the explicit constant `n` multiplying
the range diameter. There is no dependence on the partition lengths. -/
theorem eVariationOn_le_of_finite_monotone_partition
    (f : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ) (ht : MonotoneOn t (Icc 0 n))
    (hf : ∀ j < n, MonotoneOn f (Icc (t j) (t (j + 1))) ∨
      AntitoneOn f (Icc (t j) (t (j + 1)))) (B : ℝ)
    (hB : ∀ x ∈ Icc (t 0) (t n), ∀ y ∈ Icc (t 0) (t n), |f x - f y| ≤ B) :
    eVariationOn f (Icc (t 0) (t n)) ≤ (n : ℝ≥0∞) * ENNReal.ofReal B := by
  rw [eVariationOn_Icc_eq_sum_adjacent f t n ht]
  calc
    ∑ j ∈ Finset.range n, eVariationOn f (Icc (t j) (t (j + 1))) ≤
        ∑ _j ∈ Finset.range n, ENNReal.ofReal B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have h0j : t 0 ≤ t j := ht ⟨le_rfl, Nat.zero_le _⟩
        ⟨Nat.zero_le _, hjn.le⟩ (Nat.zero_le _)
      have hjsn : t (j + 1) ≤ t n := ht ⟨Nat.zero_le _, hjn⟩
        ⟨Nat.zero_le _, le_rfl⟩ hjn
      have hstep : t j ≤ t (j + 1) := ht ⟨Nat.zero_le _, hjn.le⟩
        ⟨Nat.zero_le _, hjn⟩ (Nat.le_succ _)
      exact eVariationOn_Icc_le_of_monotone_range f hstep (hf j hjn) B
        (fun x hx y hy => hB x ⟨h0j.trans hx.1, hx.2.trans hjsn⟩
          y ⟨h0j.trans hy.1, hy.2.trans hjsn⟩)
    _ = _ := by simp

/-- The extended bound proves finiteness before converting variation to a real. -/
theorem boundedVariationOn_of_finite_monotone_partition
    (f : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ) (ht : MonotoneOn t (Icc 0 n))
    (hf : ∀ j < n, MonotoneOn f (Icc (t j) (t (j + 1))) ∨
      AntitoneOn f (Icc (t j) (t (j + 1)))) (B : ℝ)
    (hB : ∀ x ∈ Icc (t 0) (t n), ∀ y ∈ Icc (t 0) (t n), |f x - f y| ≤ B) :
    BoundedVariationOn f (Icc (t 0) (t n)) := by
  have h := eVariationOn_le_of_finite_monotone_partition f t n ht hf B hB
  apply ne_top_of_le_ne_top _ h
  exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top

/-- This is the real-valued total variation in the manuscript; finiteness is
returned alongside the estimate, so `toReal` cannot hide infinite variation. -/
theorem real_variation_le_of_finite_monotone_partition
    (f : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ) (ht : MonotoneOn t (Icc 0 n))
    (hf : ∀ j < n, MonotoneOn f (Icc (t j) (t (j + 1))) ∨
      AntitoneOn f (Icc (t j) (t (j + 1)))) (B : ℝ)
    (hB : ∀ x ∈ Icc (t 0) (t n), ∀ y ∈ Icc (t 0) (t n), |f x - f y| ≤ B) :
    BoundedVariationOn f (Icc (t 0) (t n)) ∧
      variationOnFromTo f Set.univ (t 0) (t n) ≤ (n : ℝ) * B := by
  have h0n : t 0 ≤ t n := ht ⟨le_rfl, Nat.zero_le _⟩
    ⟨Nat.zero_le _, le_rfl⟩ (Nat.zero_le _)
  have hB0 : 0 ≤ B := by
    simpa using hB (t 0) ⟨le_rfl, h0n⟩ (t 0) ⟨le_rfl, h0n⟩
  refine ⟨boundedVariationOn_of_finite_monotone_partition f t n ht hf B hB, ?_⟩
  rw [variationOnFromTo.eq_of_le f Set.univ h0n, Set.univ_inter]
  apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Nat.cast_nonneg _) hB0)
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast] using
    eVariationOn_le_of_finite_monotone_partition f t n ht hf B hB

/-- One common partition supplies the same piece-count constant for every function.
No bound is chosen separately after fixing a function index. -/
theorem family_variation_le_of_common_monotone_partition
    {ι : Type*} (f : ι → ℝ → ℝ) (B : ι → ℝ) (t : ℕ → ℝ) (n : ℕ)
    (ht : MonotoneOn t (Icc 0 n))
    (hf : ∀ j < n, ∀ i, MonotoneOn (f i) (Icc (t j) (t (j + 1))) ∨
      AntitoneOn (f i) (Icc (t j) (t (j + 1))))
    (hB : ∀ i, ∀ x ∈ Icc (t 0) (t n), ∀ y ∈ Icc (t 0) (t n),
      |f i x - f i y| ≤ B i) :
    ∀ i, BoundedVariationOn (f i) (Icc (t 0) (t n)) ∧
      variationOnFromTo (f i) Set.univ (t 0) (t n) ≤ (n : ℝ) * B i :=
  fun i => real_variation_le_of_finite_monotone_partition (f i) t n ht
    (fun j hj => hf j hj i) (B i) (hB i)

/-- Continuity supplies the endpoint values omitted by monotonicity on an open piece.
This also allows a degenerate or empty interval without a separate positivity premise. -/
theorem monotoneOn_Icc_of_continuousOn_Ioo (f : ℝ → ℝ) {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hm : MonotoneOn f (Ioo a b)) :
    MonotoneOn f (Icc a b) := by
  intro x hx y hy hxy
  by_cases heq : x = y
  · simp only [heq, le_refl]
  have hlt : x < y := lt_of_le_of_ne hxy heq
  have hxb : x < b := hlt.trans_le hy.2
  have hleft : ∀ z ∈ Ioo x b, f x ≤ f z := by
    intro z hz
    have haz : a < z := hx.1.trans_lt hz.1
    have hsub : closure (Ioo a z) ⊆ Icc a b := by
      rw [closure_Ioo haz]
      exact Set.Icc_subset_Icc le_rfl hz.2.le
    have hxc : x ∈ closure (Ioo a z) := by
      rw [closure_Ioo haz]
      exact ⟨hx.1, hz.1.le⟩
    exact le_on_closure (fun w hw => hm ⟨hw.1, hw.2.trans hz.2⟩ ⟨haz, hz.2⟩ hw.2.le)
      (hc.mono hsub) continuousOn_const hxc
  have hsub : closure (Ioo x b) ⊆ Icc a b := by
    rw [closure_Ioo hxb]
    exact Set.Icc_subset_Icc hx.1 le_rfl
  have hyc : y ∈ closure (Ioo x b) := by
    rw [closure_Ioo hxb]
    exact ⟨hxy, hy.2⟩
  exact le_on_closure hleft continuousOn_const (hc.mono hsub) hyc

/-- The continuous version includes decreasing pieces as well. -/
theorem monotone_or_antitone_Icc_of_continuousOn_Ioo (f : ℝ → ℝ) {a b : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hm : MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b)) :
    MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b) := by
  rcases hm with hm | hm
  · exact Or.inl (monotoneOn_Icc_of_continuousOn_Ioo f hc hm)
  · have hn : MonotoneOn (fun x => -f x) (Ioo a b) := by
      intro x hx y hy hxy
      exact neg_le_neg (hm hx hy hxy)
    have hnclosed := monotoneOn_Icc_of_continuousOn_Ioo (fun x => -f x) hc.neg hn
    right
    intro x hx y hy hxy
    exact neg_le_neg_iff.mp (hnclosed hx hy hxy)

/-- The original argument may obtain monotonicity on open analytic pieces.
The stated continuity then completes the endpoints before summing variation. -/
theorem family_variation_le_of_continuous_common_partition
    {ι : Type*} (f : ι → ℝ → ℝ) (B : ι → ℝ) (t : ℕ → ℝ) (n : ℕ)
    (ht : MonotoneOn t (Icc 0 n))
    (hc : ∀ i, ContinuousOn (f i) (Icc (t 0) (t n)))
    (hf : ∀ j < n, ∀ i, MonotoneOn (f i) (Ioo (t j) (t (j + 1))) ∨
      AntitoneOn (f i) (Ioo (t j) (t (j + 1))))
    (hB : ∀ i, ∀ x ∈ Icc (t 0) (t n), ∀ y ∈ Icc (t 0) (t n),
      |f i x - f i y| ≤ B i) :
    ∀ i, BoundedVariationOn (f i) (Icc (t 0) (t n)) ∧
      variationOnFromTo (f i) Set.univ (t 0) (t n) ≤ (n : ℝ) * B i := by
  apply family_variation_le_of_common_monotone_partition f B t n ht _ hB
  intro j hj i
  apply monotone_or_antitone_Icc_of_continuousOn_Ioo (f i) _ (hf j hj i)
  exact (hc i).mono (Set.Icc_subset_Icc
    (ht ⟨le_rfl, Nat.zero_le _⟩ ⟨Nat.zero_le _, hj.le⟩ (Nat.zero_le _))
    (ht ⟨Nat.zero_le _, hj⟩ ⟨Nat.zero_le _, le_rfl⟩ hj))

/-- A path inside the source set inherits each prescribed range interval. The same
subdivision then bounds every composed function by the same piece count. -/
theorem family_path_variation_le_of_common_partition
    {X ι : Type*} (S : Set X) (γ : ℝ → X) (F : ι → X → ℝ)
    (L U B : ι → ℝ) (t : ℕ → ℝ) (n : ℕ) (ht : MonotoneOn t (Icc 0 n))
    (hγ : Set.MapsTo γ (Icc (t 0) (t n)) S)
    (hrange : ∀ i, ∀ x ∈ S, F i x ∈ Icc (L i) (U i))
    (hwidth : ∀ i, U i - L i ≤ B i)
    (hc : ∀ i, ContinuousOn (fun z => F i (γ z)) (Icc (t 0) (t n)))
    (hf : ∀ j < n, ∀ i, MonotoneOn (fun z => F i (γ z)) (Ioo (t j) (t (j + 1))) ∨
      AntitoneOn (fun z => F i (γ z)) (Ioo (t j) (t (j + 1)))) :
    ∀ i, BoundedVariationOn (fun z => F i (γ z)) (Icc (t 0) (t n)) ∧
      variationOnFromTo (fun z => F i (γ z)) Set.univ (t 0) (t n) ≤ (n : ℝ) * B i := by
  apply family_variation_le_of_continuous_common_partition
    (fun i z => F i (γ z)) B t n ht hc hf
  intro i x hx y hy
  have hfx := hrange i (γ x) (hγ hx)
  have hfy := hrange i (γ y) (hγ hy)
  exact (abs_sub_le_iff.mpr ⟨sub_le_sub hfx.2 hfy.1, sub_le_sub hfy.2 hfx.1⟩).trans
    (hwidth i)

end PaperI
