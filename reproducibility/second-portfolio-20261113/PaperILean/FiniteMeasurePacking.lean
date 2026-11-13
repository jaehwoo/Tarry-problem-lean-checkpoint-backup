import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

/-! Finite disjoint packing from a positive equal-mass bound in a probability
space. Existence and maximality are proved, not assumed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace PaperI

theorem exists_finset_max_card {ι : Type*} (P : Finset ι → Prop)
    (hempty : P ∅) (N : ℕ) (hbound : ∀ s, P s → s.card ≤ N) :
    ∃ s, P s ∧ ∀ t, P t → t.card ≤ s.card := by
  let A : Set ℕ := Finset.card '' {s | P s}
  have hfin : A.Finite := (Set.finite_Iic N).subset (by
    rintro n ⟨s, hs, rfl⟩
    exact hbound s hs)
  have hne : A.Nonempty := ⟨0, ∅, hempty, rfl⟩
  obtain ⟨_, ⟨s, hs, rfl⟩, hmax⟩ := Set.exists_max_image A id hfin hne
  exact ⟨s, hs, fun t ht => hmax _ ⟨t, ht, rfl⟩⟩

theorem finiteMeasurePacking_card_bound {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (V : ι → Set α)
    (hV : ∀ i, MeasurableSet (V i)) (m : ℝ) (hm : 0 < m)
    (hvol : ∀ i, μ.real (V i) = m) (s : Finset ι)
    (hdisj : (↑s : Set ι).PairwiseDisjoint V) :
    (s.card : ℝ) ≤ 1 / m := by
  have hle : μ.real (⋃ i ∈ s, V i) ≤ 1 := by
    simpa only [measureReal_univ_eq_one] using
      (measureReal_mono (μ := μ) (subset_univ (⋃ i ∈ s, V i)))
  rw [measureReal_biUnion_finset hdisj (fun i _ => hV i)] at hle
  simp only [hvol, Finset.sum_const, nsmul_eq_mul] at hle
  exact (le_div_iff₀ hm).mpr hle

theorem finiteMeasurePacking_exists {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (V : ι → Set α)
    (hV : ∀ i, MeasurableSet (V i)) (m : ℝ) (hm : 0 < m)
    (hvol : ∀ i, μ.real (V i) = m) :
    ∃ s : Finset ι, (↑s : Set ι).PairwiseDisjoint V ∧
      (s.card : ℝ) ≤ 1 / m ∧
      (∀ t : Finset ι, (↑t : Set ι).PairwiseDisjoint V → t.card ≤ s.card) ∧
      ∀ i, ∃ j ∈ s, ¬ Disjoint (V i) (V j) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / m)
  have hbound (s : Finset ι) (hs : (↑s : Set ι).PairwiseDisjoint V) : s.card ≤ N := by
    have h := (finiteMeasurePacking_card_bound μ V hV m hm hvol s hs).trans hN
    exact_mod_cast h
  obtain ⟨s, hs, hmax⟩ := exists_finset_max_card
    (fun s : Finset ι => (↑s : Set ι).PairwiseDisjoint V)
    (by simp) N hbound
  refine ⟨s, hs, finiteMeasurePacking_card_bound μ V hV m hm hvol s hs, hmax, ?_⟩
  intro i
  by_contra hnone
  push_neg at hnone
  have hself : ¬ Disjoint (V i) (V i) := by
    intro h
    have hempty : V i = ∅ := disjoint_self.mp h
    have hz := hvol i
    rw [hempty, measureReal_empty] at hz
    linarith
  have his : i ∉ s := fun hi => hself (hnone i hi)
  have hins : (↑(insert i s) : Set ι).PairwiseDisjoint V := by
    rw [Finset.coe_insert]
    exact hs.insert_of_not_mem his (fun j hj => hnone j hj)
  have hc := hmax (insert i s) hins
  rw [Finset.card_insert_of_not_mem his] at hc
  omega

end PaperI
