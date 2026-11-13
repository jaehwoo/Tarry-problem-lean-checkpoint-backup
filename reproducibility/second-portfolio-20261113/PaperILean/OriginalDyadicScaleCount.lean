import PaperILean.RQDyadicBins
import PaperILean.BufferedComponentIndexPacking

/-! I1259: count the original lower-inclusive, upper-exclusive distance cores.
The normalized logarithm is a separately recorded repair of the missing
small-radius convention in I1243; the manuscript itself is unchanged. -/
noncomputable section
namespace PaperI

def originalDyadicScaleWindow (δ U : ℝ) : Finset ℤ :=
  if δ ≤ U then Finset.Icc (rqDyadicExponent δ) (rqDyadicExponent U) else ∅

theorem originalDyadicScaleWindow_empty {δ U : ℝ} (h : U < δ) :
    originalDyadicScaleWindow δ U = ∅ := by
  simp [originalDyadicScaleWindow, not_le.mpr h]

theorem originalDyadicScaleWindow_self (δ : ℝ) :
    originalDyadicScaleWindow δ δ = {rqDyadicExponent δ} := by
  simp [originalDyadicScaleWindow]

theorem originalDyadicScaleWindow_mem {δ U r : ℝ} (hδ : 0 < δ)
    (hl : δ ≤ r) (hu : r ≤ U) {k : ℤ}
    (hk : (2:ℝ)^k ≤ r ∧ r < 2*(2:ℝ)^k) :
    k ∈ originalDyadicScaleWindow δ U := by
  rw [originalDyadicScaleWindow, if_pos (hl.trans hu)]
  rw [rq_dyadic_exponent_unique r (hδ.trans_le hl) k hk.1 hk.2]
  exact Finset.mem_Icc.mpr ⟨Int.log_mono_right hδ hl,
    Int.log_mono_right (hδ.trans_le hl) hu⟩

theorem originalDyadicScaleWindow_card {δ U : ℝ} (h : δ ≤ U) :
    (originalDyadicScaleWindow δ U).card =
      (rqDyadicExponent U + 1 - rqDyadicExponent δ).toNat := by
  simp [originalDyadicScaleWindow,h,Int.card_Icc]

theorem originalDyadicScaleWindow_card_le {δ U : ℝ} (hδ : 0 < δ) (h : δ ≤ U) :
    ((originalDyadicScaleWindow δ U).card : ℝ) ≤ 2 + Real.logb 2 (U/δ) := by
  rw [originalDyadicScaleWindow_card h]
  exact rq_dyadic_interval_card_bound δ U hδ h

theorem originalDyadicScaleWindow_card_le_max {δ U : ℝ} (hδ : 0 < δ) :
    ((originalDyadicScaleWindow δ U).card : ℝ) ≤ max 0 (2 + Real.logb 2 (U/δ)) := by
  by_cases h : δ ≤ U
  · exact (originalDyadicScaleWindow_card_le hδ h).trans (le_max_right _ _)
  · simp only [originalDyadicScaleWindow,if_neg h,Finset.card_empty,Nat.cast_zero]
    exact le_max_left _ _

theorem originalDyadicScaleWindow_upper_boundary (k : ℤ) :
    rqDyadicExponent (2*(2:ℝ)^k) = k+1 := by
  apply (rq_dyadic_exponent_unique _ (by positivity) (k+1) _ _).symm
  · simp [zpow_add₀ (by norm_num : (2:ℝ)≠0),mul_comm]
  · have hp : 0 < (2:ℝ)^k := zpow_pos (by norm_num) _
    rw [zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one]
    nlinarith

/-- The explicit pre-absorption bound retains the fixed buffer exponent q. -/
theorem originalDyadicScaleWindow_inverse_power_bound (q : ℕ) {P T : ℝ}
    (hP : 2 ≤ P) (hT : 0 ≤ T) :
    ((originalDyadicScaleWindow (P^q)⁻¹ (3*T+1)).card : ℝ) ≤
      2 + (Real.log 4 + Real.log (max 1 T) + (q:ℝ)*Real.log P)/Real.log 2 := by
  have hp : 0 < P := by linarith
  have hpow : 1 ≤ P^q := one_le_pow₀ (by linarith : (1:ℝ)≤P)
  have hδ : 0 < (P^q)⁻¹ := inv_pos.mpr (pow_pos hp _)
  have hδ1 : (P^q)⁻¹ ≤ 1 := (inv_le_one₀ (pow_pos hp _)).mpr hpow
  have hu : 0 < 3*T+1 := by linarith
  have hm : 0 < max 1 T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hupper : 3*T+1 ≤ 4*max 1 T := by
    have := le_max_left (1:ℝ) T
    have := le_max_right (1:ℝ) T
    linarith
  have hlog := Real.log_le_log hu hupper
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hm.ne'] at hlog
  calc
    _ ≤ 2 + Real.logb 2 ((3*T+1)/(P^q)⁻¹) :=
      originalDyadicScaleWindow_card_le hδ (by linarith)
    _ = 2 + (Real.log (3*T+1)+(q:ℝ)*Real.log P)/Real.log 2 := by
      rw [Real.logb,Real.log_div hu.ne' hδ.ne',Real.log_inv,Real.log_pow]
      ring
    _ ≤ _ := by
      apply add_le_add_left
      exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos (by norm_num)).le

theorem originalDyadicScaleWindow_polynomial_log_bound (q : ℕ) :
    ∃ n : ℕ, ∀ P T : ℝ, 2 ≤ P → 0 ≤ T →
      ((originalDyadicScaleWindow (P^q)⁻¹ (3*T+1)).card : ℝ) ≤
        P^n * (1 + Real.log (max 1 T)) := by
  let K : ℝ := 2 + (Real.log 4 + 1 + (q:ℝ))/Real.log 2
  obtain ⟨m,hm⟩ := uniform_constant_le_power K
  refine ⟨m+1,?_⟩
  intro P T hP hT
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl : 0 ≤ Real.log (max 1 T) := Real.log_nonneg (le_max_left _ _)
  have hlogP : Real.log P ≤ P := Real.log_le_self (by linarith)
  have hq : 0 ≤ (q:ℝ) := Nat.cast_nonneg q
  have hmul := mul_le_mul_of_nonneg_left hlogP hq
  have hL : 1 ≤ 1 + Real.log (max 1 T) := by linarith
  have hbase : 2+(Real.log 4 + Real.log (max 1 T)+(q:ℝ)*Real.log P)/Real.log 2 ≤
      K*P*(1+Real.log (max 1 T)) := by
    have hPL : 1 ≤ P*(1+Real.log (max 1 T)) :=
      by nlinarith [mul_nonneg (by linarith : 0 ≤ P) hl]
    have hLPL : 1+Real.log (max 1 T) ≤ P*(1+Real.log (max 1 T)) :=
      le_mul_of_one_le_left (by linarith) (by linarith)
    have hPPL : P ≤ P*(1+Real.log (max 1 T)) :=
      le_mul_of_one_le_right (by linarith) hL
    have ha := mul_le_mul_of_nonneg_left hPL h4
    have hb := mul_le_mul_of_nonneg_left (hlogP.trans hPPL) hq
    calc
      _ ≤ 2*(P*(1+Real.log (max 1 T))) +
          ((Real.log 4+1+(q:ℝ))*(P*(1+Real.log (max 1 T))))/Real.log 2 := by
        apply add_le_add (by linarith)
        apply div_le_div_of_nonneg_right _ h2.le
        nlinarith
      _ = _ := by dsimp [K]; ring
  calc
    _ ≤ 2+(Real.log 4+Real.log (max 1 T)+(q:ℝ)*Real.log P)/Real.log 2 :=
      originalDyadicScaleWindow_inverse_power_bound q hP hT
    _ ≤ K*P*(1+Real.log (max 1 T)) := hbase
    _ ≤ P^m*P*(1+Real.log (max 1 T)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hm P hP) (by linarith))
        (by linarith)
    _ = _ := by rw [pow_succ]

theorem originalDyadicScaleWindow_manuscript_range_bound (q : ℕ) :
    ∃ n : ℕ, ∀ P T : ℝ, 2 ≤ P → 2 ≤ T →
      ((originalDyadicScaleWindow (P^q)⁻¹ (3*T+1)).card : ℝ) ≤
        P^n * (1 + Real.log T) := by
  obtain ⟨n,hn⟩ := originalDyadicScaleWindow_polynomial_log_bound q
  refine ⟨n,?_⟩
  intro P T hP hT
  simpa only [max_eq_right (by linarith : (1:ℝ)≤T)] using hn P T hP (by linarith)

/-- A literal one-scale bound by C*(1+log T) fails at this positive radius.
This certifies the scalar obstruction, not the full geometric counterexample. -/
theorem original_distance_scale_small_radius_obstruction (C : ℝ) :
    ¬ ((originalDyadicScaleWindow (Real.exp (-1)/2) (Real.exp (-1)/2)).card : ℝ) ≤
        C*(1+Real.log (Real.exp (-1))) := by
  simp [originalDyadicScaleWindow_self,Real.log_exp]

theorem original_inverse_real_power_minorant (c : ℝ) :
    ∃ q : ℕ, ∀ P : ℝ, 2 ≤ P → (P^q)⁻¹ ≤ P^(-c) := by
  obtain ⟨q,hq⟩ := exists_nat_ge c
  refine ⟨q,?_⟩
  intro P hP
  have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ P) (neg_le_neg hq)
  simpa only [Real.rpow_neg (by linarith : 0 ≤ P),Real.rpow_natCast] using h

end PaperI
