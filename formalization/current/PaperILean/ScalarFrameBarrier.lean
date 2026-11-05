import PaperILean.FrameEnergy

/-! Positive scalar barrier used at Paper I 246. All sublevel constants depend
only on the height. The value at zero is never included in the domain. -/
noncomputable section
open scoped BigOperators
namespace PaperI

def scalarFrameBarrier (s : ℝ) : ℝ := s ^ 2 - 2 * Real.log s

theorem scalarFrameBarrier_ge_square (s : ℝ) (hs : 0 < s) :
    (s - 1) ^ 2 + 1 ≤ scalarFrameBarrier s := by
  have h := Real.log_le_sub_one_of_pos hs
  unfold scalarFrameBarrier
  nlinarith

theorem scalarFrameBarrier_ge_one (s : ℝ) (hs : 0 < s) :
    1 ≤ scalarFrameBarrier s := by
  have h := scalarFrameBarrier_ge_square s hs
  nlinarith [sq_nonneg (s - 1)]

theorem scalarFrameBarrier_nonneg (s : ℝ) (hs : 0 < s) :
    0 ≤ scalarFrameBarrier s := le_trans (by norm_num) (scalarFrameBarrier_ge_one s hs)

theorem scalarFrameBarrier_sublevel_lower (s M : ℝ) (hs : 0 < s)
    (hM : scalarFrameBarrier s ≤ M) : Real.exp (-M / 2) ≤ s := by
  apply (Real.le_log_iff_exp_le hs).mp
  unfold scalarFrameBarrier at hM
  nlinarith [sq_nonneg s]

theorem scalarFrameBarrier_sublevel_upper (s M : ℝ) (hs : 0 < s)
    (hM : scalarFrameBarrier s ≤ M) : s ≤ 1 + Real.sqrt M := by
  have h := (scalarFrameBarrier_ge_square s hs).trans hM
  have hnon : 0 ≤ M := (scalarFrameBarrier_nonneg s hs).trans hM
  have heq := Real.sq_sqrt hnon
  have hp := Real.sqrt_nonneg M
  nlinarith

theorem scalarFrameBarrier_sum_ge_card {n : ℕ} (s : Fin n → ℝ)
    (hs : ∀ i, 0 < s i) : (n : ℝ) ≤ ∑ i, scalarFrameBarrier (s i) := by
  simpa using Finset.sum_le_sum (s := Finset.univ)
    (f := fun _ : Fin n => (1 : ℝ)) (fun i _ => scalarFrameBarrier_ge_one (s i) (hs i))

theorem scalarFrameBarrier_le_sum {n : ℕ} (s : Fin n → ℝ)
    (hs : ∀ i, 0 < s i) (i : Fin n) :
    scalarFrameBarrier (s i) ≤ ∑ j, scalarFrameBarrier (s j) :=
  Finset.single_le_sum (fun j _ => scalarFrameBarrier_nonneg (s j) (hs j)) (Finset.mem_univ i)

theorem scalarFrameBarrier_sum_sublevel_bounds {n : ℕ} (s : Fin n → ℝ)
    (hs : ∀ i, 0 < s i) (M : ℝ) (hM : ∑ i, scalarFrameBarrier (s i) ≤ M) (i : Fin n) :
    Real.exp (-M / 2) ≤ s i ∧ s i ≤ 1 + Real.sqrt M := by
  have hi := (scalarFrameBarrier_le_sum s hs i).trans hM
  exact ⟨scalarFrameBarrier_sublevel_lower _ M (hs i) hi,
    scalarFrameBarrier_sublevel_upper _ M (hs i) hi⟩

end PaperI
