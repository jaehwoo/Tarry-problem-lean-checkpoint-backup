import PaperILean.PublishedFiberFormatComponents
import Mathlib.Data.Finset.Card

noncomputable section
open scoped BigOperators

-- Pointwise existence cannot be moved before an unbounded parameter.
example : ∀ m : ℕ, ∃ N : ℕ, m ≤ N := fun m => ⟨m, le_rfl⟩
example : ¬ ∃ N : ℕ, ∀ m : ℕ, m ≤ N := by
  rintro ⟨N, hN⟩
  exact Nat.not_succ_le_self N (hN (N+1))

-- An exact family of real finite sets with unbounded cardinality.
def testRealPoints (m : ℕ) : Finset ℝ :=
  (Finset.range m).map ⟨fun j => (j : ℝ), Nat.cast_injective⟩
example (m : ℕ) : (testRealPoints m).card = m := by simp [testRealPoints]
example : ¬ ∃ N : ℕ, ∀ m : ℕ, (testRealPoints m).card ≤ N := by
  rintro ⟨N, hN⟩
  have h := hN (N+1)
  simp only [testRealPoints, Finset.card_map, Finset.card_range] at h
  omega

-- These are polynomial zero sets. Uniform format must retain a degree/count
-- bound before choosing N; qualitative semialgebraicity alone is insufficient.
example (m : ℕ) (x : ℝ) :
    (∏ j ∈ Finset.range m, (x - (j : ℝ))) = 0 ↔ x ∈ testRealPoints m := by
  classical
  simp [testRealPoints, Finset.prod_eq_zero_iff, sub_eq_zero, eq_comm]

-- The zero-member case is an empty fiber, not an assertion that its exact
-- geometric dimension equals zero. BPR's empty dimension convention is -1.
example : testRealPoints 0 = ∅ := by simp [testRealPoints]
example : (-1 : ℤ) ≤ 0 := by norm_num
example : (-1 : ℤ) ≠ 0 := by norm_num

-- Keeping one N for components and dimension-zero cardinality is meaningful:
-- conjunctions can be assembled without choosing a second parameter-dependent N.
example {P : Type} (C K : P → ℕ) (zeroDim : P → Prop) (N : ℕ)
    (hC : ∀ p, C p ≤ N) (hK : ∀ p, zeroDim p → K p = C p) :
    ∀ p, C p ≤ N ∧ (zeroDim p → K p ≤ N) := by
  intro p
  exact ⟨hC p, fun hp => (hK p hp).trans_le (hC p)⟩
