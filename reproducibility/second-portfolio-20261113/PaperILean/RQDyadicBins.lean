import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! I454–458: unique lower-inclusive dyadic bins for positive diagonal entries.
The triple bins are not ordered singular-value triples. The finite count is
uniform in the scale and depends only on the ratio of the interval endpoints. -/
noncomputable section
open scoped BigOperators
namespace PaperI

def rqDyadicExponent (r : ℝ) : ℤ := Int.log 2 r
def rqDyadicScale (r : ℝ) : ℝ := 2 ^ rqDyadicExponent r

theorem rq_dyadic_scale_pos (r : ℝ) : 0 < rqDyadicScale r := by
  exact zpow_pos (by norm_num) _

theorem rq_dyadic_bounds (r : ℝ) (hr : 0 < r) :
    rqDyadicScale r ≤ r ∧ r < 2 * rqDyadicScale r := by
  refine ⟨Int.zpow_log_le_self (by norm_num) hr, ?_⟩
  simpa only [rqDyadicScale, rqDyadicExponent, Nat.cast_ofNat, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    zpow_one, mul_comm] using Int.lt_zpow_succ_log_self (by norm_num : 1 < 2) r

theorem rq_dyadic_exponent_unique (r : ℝ) (hr : 0 < r) (z : ℤ)
    (hl : (2 : ℝ)^z ≤ r) (hu : r < 2 * (2 : ℝ)^z) : z = rqDyadicExponent r := by
  have hl' : z ≤ Int.log 2 r := (Int.zpow_le_iff_le_log (by norm_num) hr).mp hl
  have hu' : Int.log 2 r < z + 1 := (Int.lt_zpow_iff_log_lt (by norm_num) hr).mp (by
    simpa only [Nat.cast_ofNat, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm] using hu)
  unfold rqDyadicExponent
  omega

theorem rq_dyadic_ratio (r : ℝ) (hr : 0 < r) :
    1 ≤ r / rqDyadicScale r ∧ r / rqDyadicScale r < 2 := by
  have h := rq_dyadic_bounds r hr
  exact ⟨(one_le_div (rq_dyadic_scale_pos r)).mpr h.1,
    (div_lt_iff₀ (rq_dyadic_scale_pos r)).mpr h.2⟩

def rqDyadicTripleBins (a b : ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (rqDyadicExponent a) (rqDyadicExponent b))

theorem rq_dyadic_triple_mem (a b : ℝ) (ha : 0 < a) (r : Fin 3 → ℝ)
    (hr : ∀ i, a ≤ r i ∧ r i ≤ b) :
    (fun i => rqDyadicExponent (r i)) ∈ rqDyadicTripleBins a b := by
  apply Fintype.mem_piFinset.mpr
  intro i
  exact Finset.mem_Icc.mpr ⟨Int.log_mono_right ha (hr i).1,
    Int.log_mono_right (ha.trans_le (hr i).1) (hr i).2⟩

theorem rq_dyadic_triple_card (a b : ℝ) :
    (rqDyadicTripleBins a b).card =
      (rqDyadicExponent b + 1 - rqDyadicExponent a).toNat ^ 3 := by
  simp [rqDyadicTripleBins, Int.card_Icc]

theorem rq_dyadic_interval_card_bound (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ((rqDyadicExponent b + 1 - rqDyadicExponent a).toNat : ℝ) ≤
      2 + Real.logb 2 (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  have hm : rqDyadicExponent a ≤ rqDyadicExponent b := Int.log_mono_right ha hab
  have hn : 0 ≤ rqDyadicExponent b + 1 - rqDyadicExponent a := by omega
  have hc : ((rqDyadicExponent b + 1 - rqDyadicExponent a).toNat : ℝ) =
      (rqDyadicExponent b : ℝ) + 1 - (rqDyadicExponent a : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  rw [hc, Real.logb_div hb.ne' ha.ne']
  have hl := Int.lt_floor_add_one (Real.logb 2 a)
  have hu := Int.floor_le (Real.logb 2 b)
  have heqa : ⌊Real.logb 2 a⌋ = Int.log 2 a := by
    simpa using Real.floor_logb_natCast (b := 2) ha.le
  have heqb : ⌊Real.logb 2 b⌋ = Int.log 2 b := by
    simpa using Real.floor_logb_natCast (b := 2) hb.le
  rw [heqa] at hl
  rw [heqb] at hu
  change Real.logb 2 a < (rqDyadicExponent a : ℝ) + 1 at hl
  change (rqDyadicExponent b : ℝ) ≤ Real.logb 2 b at hu
  linarith

theorem rq_dyadic_triple_card_bound (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ((rqDyadicTripleBins a b).card : ℝ) ≤ (2 + Real.logb 2 (b / a)) ^ 3 := by
  rw [rq_dyadic_triple_card, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (rq_dyadic_interval_card_bound a b ha hab) 3

end PaperI
