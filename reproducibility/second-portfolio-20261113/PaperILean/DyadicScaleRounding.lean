import PaperILean.BufferedComponentIndexPacking
import Mathlib.Data.Nat.Find

/-! I1265: replace sub-unit lengths by one and round upwards to the least
nonnegative dyadic power. No geometric set is enlarged by this definition. -/
noncomputable section
namespace PaperI

theorem exists_dyadic_scale_above (x : ℝ) : ∃ n : ℕ, x ≤ (2 : ℝ)^n := by
  obtain ⟨n,hn⟩ := exists_nat_ge x
  exact ⟨n,hn.trans (by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le)⟩

def roundedDyadicScaleIndex (x : ℝ) : ℕ :=
  @Nat.find (fun n => x ≤ (2 : ℝ)^n) (Classical.decPred _) (exists_dyadic_scale_above x)

def roundedDyadicScale (x : ℝ) : ℝ := (2 : ℝ)^(roundedDyadicScaleIndex x)

theorem le_roundedDyadicScale (x : ℝ) : x ≤ roundedDyadicScale x :=
  Nat.find_spec (exists_dyadic_scale_above x)

theorem one_le_roundedDyadicScale (x : ℝ) : 1 ≤ roundedDyadicScale x :=
  one_le_pow₀ (by norm_num)

theorem roundedDyadicScale_pos (x : ℝ) : 0 < roundedDyadicScale x :=
  zero_lt_one.trans_le (one_le_roundedDyadicScale x)

theorem roundedDyadicScaleIndex_mono : Monotone roundedDyadicScaleIndex := by
  intro x y hxy
  exact Nat.find_mono (fun _ hn => hxy.trans hn)

theorem roundedDyadicScale_mono : Monotone roundedDyadicScale := by
  intro x y hxy
  exact pow_le_pow_right₀ (by norm_num) (roundedDyadicScaleIndex_mono hxy)

theorem roundedDyadicScale_eq_one_of_le_one {x : ℝ} (hx : x ≤ 1) :
    roundedDyadicScale x = 1 := by
  have h : roundedDyadicScaleIndex x ≤ 0 := Nat.find_min' _ (by simpa using hx)
  simp [roundedDyadicScale,Nat.eq_zero_of_le_zero h]

theorem roundedDyadicScale_lt_two_max (x : ℝ) :
    roundedDyadicScale x < 2*max 1 x := by
  have hmax : 1 ≤ max (1 : ℝ) x := le_max_left _ _
  generalize hn : roundedDyadicScaleIndex x = n
  cases n with
  | zero => simp only [roundedDyadicScale,hn,pow_zero]; linarith
  | succ n =>
    have hlt : n < roundedDyadicScaleIndex x := by omega
    have h := Nat.find_min (exists_dyadic_scale_above x) hlt
    have hx : (2 : ℝ)^n < x := lt_of_not_ge h
    simp only [roundedDyadicScale,hn,pow_succ]
    nlinarith [le_max_right (1 : ℝ) x]

theorem roundedDyadicScale_dyadic (x : ℝ) :
    ∃ n : ℕ, roundedDyadicScale x = (2 : ℝ)^n := ⟨_,rfl⟩

theorem roundedDyadicScale_measurable : Measurable roundedDyadicScale :=
  roundedDyadicScale_mono.measurable

theorem roundedDyadicScale_le_of_multiplier {x A : ℝ}
    (hA : 1 ≤ A) (hAx : 1 ≤ A*x) : roundedDyadicScale x ≤ 2*A*x := by
  have hx : 0 < x := by nlinarith
  have hmax : max 1 x ≤ A*x := max_le hAx (by nlinarith)
  exact (roundedDyadicScale_lt_two_max x).le.trans (by nlinarith)

/-- m depends only on c; q and every real scale are quantified afterwards. -/
theorem uniform_roundedDyadicScale_power_comparison (c : ℝ) (hc : 0 < c) :
    ∃ m : ℕ, ∀ (P : ℝ) (q : ℕ), 2 ≤ P → ∀ x : ℝ,
      c*(P^q)⁻¹ ≤ x →
      0 < x ∧ x ≤ roundedDyadicScale x ∧
        roundedDyadicScale x ≤ P^(m+q+1)*x := by
  obtain ⟨m,hm⟩ := uniform_constant_le_power (max 1 c⁻¹)
  refine ⟨m,?_⟩
  intro P q hP x hx
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hP1 : 1 ≤ P := by linarith
  have hpq : 0 < P^q := pow_pos hP0 q
  have hx0 : 0 < x := (mul_pos hc (inv_pos.mpr hpq)).trans_le hx
  have hcm : c⁻¹ ≤ P^m := (le_max_right _ _).trans (hm P hP)
  have hcq : c ≤ P^q*x := by
    have h := mul_le_mul_of_nonneg_left hx hpq.le
    field_simp at h
    nlinarith
  have hprod : 1 ≤ P^(m+q)*x := by
    calc
      1 = c⁻¹*c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ P^m*(P^q*x) := mul_le_mul hcm hcq hc.le (pow_nonneg hP0.le m)
      _ = _ := by rw [pow_add]; ring
  refine ⟨hx0,le_roundedDyadicScale x,?_⟩
  calc
    roundedDyadicScale x ≤ 2*P^(m+q)*x :=
      roundedDyadicScale_le_of_multiplier (one_le_pow₀ hP1) hprod
    _ ≤ P*P^(m+q)*x := by gcongr
    _ = P^(m+q+1)*x := by rw [pow_succ]; ring

end PaperI
