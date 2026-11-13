import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Explicit small-radius correction for I1243--1259.
The manuscript is unchanged. Only the radius-dependent logarithmic count
is normalized; physical sets, distances, components, paths and scales are not.
-/
noncomputable section
namespace PaperI

def planarLogSize (T : ℝ) : ℝ := 1 + Real.log (max 1 T)

theorem planarLogSize_one_le (T : ℝ) : 1 ≤ planarLogSize T := by
  have h := Real.log_nonneg (le_max_left (1 : ℝ) T)
  dsimp [planarLogSize]
  linarith

theorem planarLogSize_pos (T : ℝ) : 0 < planarLogSize T :=
  zero_lt_one.trans_le (planarLogSize_one_le T)

theorem planarLogSize_eq_one {T : ℝ} (hT : T ≤ 1) : planarLogSize T = 1 := by
  simp [planarLogSize, max_eq_left hT]

theorem planarLogSize_eq_printed {T : ℝ} (hT : 1 ≤ T) :
    planarLogSize T = 1 + Real.log T := by
  simp [planarLogSize, max_eq_right hT]

theorem planarLogSize_mono : Monotone planarLogSize := by
  intro T U h
  exact add_le_add_left (Real.log_le_log
    (zero_lt_one.trans_le (le_max_left _ _)) (max_le_max_left 1 h)) 1

theorem continuous_planarLogSize : Continuous planarLogSize := by
  exact continuous_const.add ((continuous_const.max continuous_id).log
    (fun T => ne_of_gt (zero_lt_one.trans_le (le_max_left (1 : ℝ) T))))

/-- Actual positive radius of the earlier zero-factor obstruction. -/
theorem planarLogSize_at_obstruction : planarLogSize (Real.exp (-1)) = 1 := by
  apply planarLogSize_eq_one
  exact (Real.exp_le_one_iff).mpr (by norm_num)

theorem original_printed_log_power_obstruction (C : ℝ) {n : ℕ} (hn : 0 < n) :
    ¬ (1 : ℝ) ≤ C * (1 + Real.log (Real.exp (-1))) ^ n := by
  simp [Real.log_exp, zero_pow (Nat.ne_of_gt hn)]

/-- A radius normalized to at least two costs only a universal factor. -/
theorem planar_radius_two_le (T : ℝ) : max 2 T ≤ 2 * max 1 T := by
  have h1 := le_max_left (1 : ℝ) T
  have hT := le_max_right (1 : ℝ) T
  exact max_le (by linarith) (by linarith)

theorem planar_log_radius_two_le (T : ℝ) :
    Real.log (max 2 T) ≤ Real.log 2 + Real.log (max 1 T) := by
  have hm : 0 < max 1 T := zero_lt_one.trans_le (le_max_left _ _)
  have h := Real.log_le_log
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _))
    (planar_radius_two_le T)
  simpa only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hm.ne'] using h

theorem planarLogSize_radius_two_le (T : ℝ) :
    1 + Real.log (max 2 T) ≤ (1 + Real.log 2) * planarLogSize T := by
  have h := planar_log_radius_two_le T
  have hp := Real.log_nonneg (le_max_left (1 : ℝ) T)
  have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  dsimp [planarLogSize]
  nlinarith [mul_nonneg h2 hp]

/-- Fixed exponent n is upgraded before P,T; no T-dependent constant. -/
theorem planarLogSize_single_exponent {P T : ℝ} (hP : 1 ≤ P) (n : ℕ) :
    P^n * planarLogSize T ≤ P^(n+1) * (planarLogSize T)^(n+1) := by
  exact mul_le_mul (pow_le_pow_right₀ hP (Nat.le_succ n))
    (le_self_pow₀ (planarLogSize_one_le T) (Nat.succ_ne_zero n))
    (planarLogSize_pos T).le (pow_nonneg (zero_le_one.trans hP) _)

/-- Enlarging a bounding radius does not spoil the physical logarithmic loss.
This only assumes the original radius upper bound; geometry is unchanged. -/
theorem planarLogSize_physical_bound (a : ℕ) {P d T : ℝ}
    (hP : 1 ≤ P) (hd : 0 < d) (hd1 : d ≤ 1) (hT : T ≤ P^a / d) :
    planarLogSize T ≤ 1 + (a : ℝ) * Real.log P + Real.log d⁻¹ := by
  have hp : 0 < P := zero_lt_one.trans_le hP
  have hq : 1 ≤ P^a / d := (le_div_iff₀ hd).mpr (by
    simpa using hd1.trans (one_le_pow₀ hP))
  have h := Real.log_le_log (zero_lt_one.trans_le (le_max_left (1 : ℝ) T))
    (max_le hq hT)
  rw [Real.log_div (pow_pos hp a).ne' hd.ne', Real.log_pow] at h
  rw [Real.log_inv]
  dsimp [planarLogSize]
  linarith

/-- The physical comparison also retains arbitrary nonnegative real powers. -/
theorem planarLogSize_physical_real_bound {a P d T : ℝ}
    (ha : 0 ≤ a) (hP : 1 ≤ P) (hd : 0 < d) (hd1 : d ≤ 1)
    (hT : T ≤ P^a / d) :
    planarLogSize T ≤ 1 + a * Real.log P + Real.log d⁻¹ := by
  have hp : 0 < P := zero_lt_one.trans_le hP
  have hq : 1 ≤ P^a / d := (le_div_iff₀ hd).mpr (by
    simpa using hd1.trans (Real.one_le_rpow hP ha))
  have h := Real.log_le_log (zero_lt_one.trans_le (le_max_left (1 : ℝ) T))
    (max_le hq hT)
  rw [Real.log_div (Real.rpow_pos_of_pos hp a).ne' hd.ne', Real.log_rpow hp] at h
  rw [Real.log_inv]
  dsimp [planarLogSize]
  linarith

theorem planar_log_radius_two_physical_bound {a P d T : ℝ}
    (ha : 0 ≤ a) (hP : 1 ≤ P) (hd : 0 < d) (hd1 : d ≤ 1)
    (hT : T ≤ P^a / d) :
    Real.log (max 2 T) ≤ Real.log 2 + a * Real.log P + Real.log d⁻¹ := by
  have h := planarLogSize_physical_real_bound ha hP hd hd1 hT
  have h2 := planar_log_radius_two_le T
  dsimp [planarLogSize] at h
  linarith

end PaperI
