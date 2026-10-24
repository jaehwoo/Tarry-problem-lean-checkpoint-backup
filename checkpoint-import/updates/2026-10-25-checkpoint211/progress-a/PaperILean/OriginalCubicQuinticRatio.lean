import PaperILean.OriginalCubicFifthProfile

/-! Pure-quintic shape ratios in the unchanged unweighted coefficient norm.
Exact obstruction diagnostics were run before selecting this route. -/
set_option maxRecDepth 8192
noncomputable section
open Filter Topology
namespace PaperI

def originalHyperbolicQuinticNormSq (a : ℝ) : ℝ := 1+25*a^2+100*a^4+100*a^6+25*a^8+a^10
def originalHyperbolicQuinticYEnergy (a : ℝ) : ℝ := 25*a^2+400*a^4+900*a^6+400*a^8+25*a^10
def originalHyperbolicQuinticXEnergy (a : ℝ) : ℝ := 25+400*a^2+900*a^4+400*a^6+25*a^8

theorem originalHyperbolicQuintic_ratio_boundary_values :
    originalHyperbolicQuinticNormSq 0 = 1 ∧ originalHyperbolicQuinticYEnergy 0 = 0 ∧
      originalHyperbolicQuinticXEnergy 0 = 25 ∧ originalHyperbolicQuinticNormSq 1 = 252 ∧
        originalHyperbolicQuinticYEnergy 1 = 1750 ∧ originalHyperbolicQuinticXEnergy 1 = 1750 := by
  norm_num [originalHyperbolicQuinticNormSq, originalHyperbolicQuinticYEnergy, originalHyperbolicQuinticXEnergy]

theorem originalHyperbolicQuintic_norm_sq_pos (a : ℝ) : 0 < originalHyperbolicQuinticNormSq a := by
  unfold originalHyperbolicQuinticNormSq
  positivity

theorem originalHyperbolicQuintic_y_energy_pos {a : ℝ} (ha : 0 < a) :
    0 < originalHyperbolicQuinticYEnergy a := by
  unfold originalHyperbolicQuinticYEnergy
  positivity

theorem originalHyperbolicQuintic_x_energy_pos (a : ℝ) : 0 < originalHyperbolicQuinticXEnergy a := by
  unfold originalHyperbolicQuinticXEnergy
  positivity

theorem originalHyperbolicQuintic_y_ratio_factor (a b : ℝ) :
    originalHyperbolicQuinticNormSq a * originalHyperbolicQuinticYEnergy b -
        originalHyperbolicQuinticNormSq b * originalHyperbolicQuinticYEnergy a =
      (b^2-a^2)*(25+400*b^2+900*b^4+400*b^6+25*b^8+400*a^2+8400*a^2*b^2+20400*a^2*b^4+9400*a^2*b^6+600*a^2*b^8+900*a^4+20400*a^4*b^2+59400*a^4*b^4+30600*a^4*b^6+2100*a^4*b^8+400*a^6+9400*a^6*b^2+30600*a^6*b^4+19600*a^6*b^6+1600*a^6*b^8+25*a^8+600*a^8*b^2+2100*a^8*b^4+1600*a^8*b^6+225*a^8*b^8) := by
  unfold originalHyperbolicQuinticNormSq originalHyperbolicQuinticYEnergy
  ring

theorem originalHyperbolicQuintic_x_ratio_factor (a b : ℝ) :
    originalHyperbolicQuinticNormSq a * originalHyperbolicQuinticXEnergy b -
        originalHyperbolicQuinticNormSq b * originalHyperbolicQuinticXEnergy a =
      (a^2-b^2)*(225+1600*b^2+2100*b^4+600*b^6+25*b^8+1600*a^2+19600*a^2*b^2+30600*a^2*b^4+9400*a^2*b^6+400*a^2*b^8+2100*a^4+30600*a^4*b^2+59400*a^4*b^4+20400*a^4*b^6+900*a^4*b^8+600*a^6+9400*a^6*b^2+20400*a^6*b^4+8400*a^6*b^6+400*a^6*b^8+25*a^8+400*a^8*b^2+900*a^8*b^4+400*a^8*b^6+25*a^8*b^8) := by
  unfold originalHyperbolicQuinticNormSq originalHyperbolicQuinticXEnergy
  ring

theorem originalHyperbolicQuintic_y_ratio_improves {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    originalHyperbolicQuinticNormSq b * originalHyperbolicQuinticYEnergy a <
      originalHyperbolicQuinticNormSq a * originalHyperbolicQuinticYEnergy b := by
  have hb : 0 < b := ha.trans hab
  have hs : 0 < b^2-a^2 := sub_pos.mpr ((sq_lt_sq₀ ha.le hb.le).mpr hab)
  have hp : 0 < (b^2-a^2)*(25+400*b^2+900*b^4+400*b^6+25*b^8+400*a^2+8400*a^2*b^2+20400*a^2*b^4+9400*a^2*b^6+600*a^2*b^8+900*a^4+20400*a^4*b^2+59400*a^4*b^4+30600*a^4*b^6+2100*a^4*b^8+400*a^6+9400*a^6*b^2+30600*a^6*b^4+19600*a^6*b^6+1600*a^6*b^8+25*a^8+600*a^8*b^2+2100*a^8*b^4+1600*a^8*b^6+225*a^8*b^8) :=
    mul_pos hs (by positivity)
  rw [← originalHyperbolicQuintic_y_ratio_factor] at hp
  exact sub_pos.mp hp

theorem originalHyperbolicQuintic_x_ratio_improves {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    originalHyperbolicQuinticNormSq b * originalHyperbolicQuinticXEnergy a <
      originalHyperbolicQuinticNormSq a * originalHyperbolicQuinticXEnergy b := by
  have ha : 0 < a := hb.trans hba
  have hs : 0 < a^2-b^2 := sub_pos.mpr ((sq_lt_sq₀ hb.le ha.le).mpr hba)
  have hp : 0 < (a^2-b^2)*(225+1600*b^2+2100*b^4+600*b^6+25*b^8+1600*a^2+19600*a^2*b^2+30600*a^2*b^4+9400*a^2*b^6+400*a^2*b^8+2100*a^4+30600*a^4*b^2+59400*a^4*b^4+20400*a^4*b^6+900*a^4*b^8+600*a^6+9400*a^6*b^2+20400*a^6*b^4+8400*a^6*b^6+400*a^6*b^8+25*a^8+400*a^8*b^2+900*a^8*b^4+400*a^8*b^6+25*a^8*b^8) :=
    mul_pos hs (by positivity)
  rw [← originalHyperbolicQuintic_x_ratio_factor] at hp
  exact sub_pos.mp hp

theorem originalHyperbolicQuintic_ratio_improvement_below {a A : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (he : originalHyperbolicQuinticNormSq a = A^4 * originalHyperbolicQuinticYEnergy a) :
    ∃ᶠ b : ℝ in 𝓝 a, 0 < b ∧ b < 1 ∧
      originalHyperbolicQuinticNormSq b < A^4 * originalHyperbolicQuinticYEnergy b := by
  apply ((frequently_gt_nhds a).and_eventually (Iio_mem_nhds ha1)).mono
  rintro b ⟨hab,hb1⟩
  refine ⟨ha.trans hab,hb1,?_⟩
  apply (mul_lt_mul_right (originalHyperbolicQuintic_y_energy_pos ha)).mp
  calc
    originalHyperbolicQuinticNormSq b * originalHyperbolicQuinticYEnergy a <
        originalHyperbolicQuinticNormSq a * originalHyperbolicQuinticYEnergy b :=
      originalHyperbolicQuintic_y_ratio_improves ha hab
    _ = (A^4 * originalHyperbolicQuinticYEnergy b) * originalHyperbolicQuinticYEnergy a := by
      rw [he]
      ring

theorem originalHyperbolicQuintic_ratio_improvement_above {a A : ℝ} (ha1 : 1 < a)
    (he : originalHyperbolicQuinticNormSq a = A^4 * originalHyperbolicQuinticXEnergy a) :
    ∃ᶠ b : ℝ in 𝓝 a, 1 < b ∧
      originalHyperbolicQuinticNormSq b < A^4 * originalHyperbolicQuinticXEnergy b := by
  apply ((frequently_lt_nhds a).and_eventually (Ioi_mem_nhds ha1)).mono
  rintro b ⟨hba,hb1⟩
  refine ⟨hb1,?_⟩
  apply (mul_lt_mul_right (originalHyperbolicQuintic_x_energy_pos a)).mp
  calc
    originalHyperbolicQuinticNormSq b * originalHyperbolicQuinticXEnergy a <
        originalHyperbolicQuinticNormSq a * originalHyperbolicQuinticXEnergy b :=
      originalHyperbolicQuintic_x_ratio_improves (by linarith) hba
    _ = (A^4 * originalHyperbolicQuinticXEnergy b) * originalHyperbolicQuinticXEnergy a := by
      rw [he]
      ring

theorem originalHyperbolicQuintic_ratio_one_strict {A : ℝ} (hA : 2 ≤ A) :
    originalHyperbolicQuinticNormSq 1 < A^4 * originalHyperbolicQuinticYEnergy 1 ∧
      originalHyperbolicQuinticNormSq 1 < A^4 * originalHyperbolicQuinticXEnergy 1 := by
  have hA2 : 4 ≤ A^2 := by nlinarith
  have hA4 : 16 ≤ A^4 := by nlinarith [sq_nonneg (A^2-4)]
  norm_num only [originalHyperbolicQuinticNormSq, originalHyperbolicQuinticYEnergy, originalHyperbolicQuinticXEnergy,
    one_pow] at ⊢
  constructor <;> nlinarith

theorem originalHyperbolicQuintic_energy_factor (a : ℝ) :
    originalHyperbolicQuinticYEnergy a = a^2 * originalHyperbolicQuinticXEnergy a := by
  unfold originalHyperbolicQuinticYEnergy originalHyperbolicQuinticXEnergy
  ring

theorem originalHyperbolicQuintic_min_below {a : ℝ} (ha : a^2 ≤ 1) :
    min (originalHyperbolicQuinticXEnergy a) (originalHyperbolicQuinticYEnergy a) = originalHyperbolicQuinticYEnergy a := by
  apply min_eq_right
  rw [originalHyperbolicQuintic_energy_factor]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right ha (originalHyperbolicQuintic_x_energy_pos a).le

theorem originalHyperbolicQuintic_min_above {a : ℝ} (ha : 1 ≤ a^2) :
    min (originalHyperbolicQuinticXEnergy a) (originalHyperbolicQuinticYEnergy a) = originalHyperbolicQuinticXEnergy a := by
  apply min_eq_left
  rw [originalHyperbolicQuintic_energy_factor]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right ha (originalHyperbolicQuintic_x_energy_pos a).le

theorem originalHyperbolicQuintic_ratio_even (a : ℝ) :
    originalHyperbolicQuinticNormSq (-a) = originalHyperbolicQuinticNormSq a ∧
      originalHyperbolicQuinticXEnergy (-a) = originalHyperbolicQuinticXEnergy a ∧
        originalHyperbolicQuinticYEnergy (-a) = originalHyperbolicQuinticYEnergy a := by
  refine ⟨?_,?_,?_⟩ <;>
    simp only [originalHyperbolicQuinticNormSq, originalHyperbolicQuinticXEnergy, originalHyperbolicQuinticYEnergy] <;> ring

theorem originalHyperbolicQuintic_min_ratio_improvement_pos {a A : ℝ} (hA : 2 ≤ A) (ha : 0 < a)
    (he : originalHyperbolicQuinticNormSq a =
      A^4 * min (originalHyperbolicQuinticXEnergy a) (originalHyperbolicQuinticYEnergy a)) :
    ∃ᶠ b : ℝ in 𝓝 a, b ≠ 0 ∧ originalHyperbolicQuinticNormSq b <
      A^4 * min (originalHyperbolicQuinticXEnergy b) (originalHyperbolicQuinticYEnergy b) := by
  rcases lt_trichotomy a 1 with ha1 | ha1 | ha1
  · have hamin := originalHyperbolicQuintic_min_below (a := a) (by nlinarith)
    rw [hamin] at he
    apply (originalHyperbolicQuintic_ratio_improvement_below ha ha1 he).mono
    rintro b ⟨hb,hb1,hstrict⟩
    rw [originalHyperbolicQuintic_min_below (a := b) (by nlinarith)]
    exact ⟨ne_of_gt hb,hstrict⟩
  · subst a
    rw [originalHyperbolicQuintic_min_below (a := 1) (by norm_num)] at he
    exact False.elim ((ne_of_lt (originalHyperbolicQuintic_ratio_one_strict hA).1) he)
  · have hamin := originalHyperbolicQuintic_min_above (a := a) (by nlinarith)
    rw [hamin] at he
    apply (originalHyperbolicQuintic_ratio_improvement_above ha1 he).mono
    rintro b ⟨hb1,hstrict⟩
    rw [originalHyperbolicQuintic_min_above (a := b) (by nlinarith)]
    exact ⟨by linarith,hstrict⟩

theorem originalHyperbolicQuintic_min_ratio_improvement {a A : ℝ} (hA : 2 ≤ A) (ha : a ≠ 0)
    (he : originalHyperbolicQuinticNormSq a =
      A^4 * min (originalHyperbolicQuinticXEnergy a) (originalHyperbolicQuinticYEnergy a)) :
    ∃ᶠ b : ℝ in 𝓝 a, b ≠ 0 ∧ originalHyperbolicQuinticNormSq b <
      A^4 * min (originalHyperbolicQuinticXEnergy b) (originalHyperbolicQuinticYEnergy b) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hne : originalHyperbolicQuinticNormSq (-a) =
        A^4 * min (originalHyperbolicQuinticXEnergy (-a)) (originalHyperbolicQuinticYEnergy (-a)) := by
      simpa only [(originalHyperbolicQuintic_ratio_even a).1, (originalHyperbolicQuintic_ratio_even a).2.1,
        (originalHyperbolicQuintic_ratio_even a).2.2] using he
    have hf := originalHyperbolicQuintic_min_ratio_improvement_pos hA (neg_pos.mpr ha) hne
    have hn : Tendsto (fun b : ℝ => -b) (𝓝 (-a)) (𝓝 a) := by
      simpa only [neg_neg] using
        (continuous_neg.continuousAt (x := -a) : ContinuousAt (fun b : ℝ => -b) (-a)).tendsto
    apply hn.frequently
    apply hf.mono
    intro b hb
    simpa only [(originalHyperbolicQuintic_ratio_even b).1, (originalHyperbolicQuintic_ratio_even b).2.1,
      (originalHyperbolicQuintic_ratio_even b).2.2, neg_ne_zero] using hb
  · exact originalHyperbolicQuintic_min_ratio_improvement_pos hA ha he


def originalCubicQuinticNormSq (s g : ℝ) : ℝ :=
  1+25*g^2+100*g^4+100*g^6+25*g^8+g^10+25*s^2+400*s^2*g^2+900*s^2*g^4+400*s^2*g^6+25*s^2*g^8+100*s^4+900*s^4*g^2+900*s^4*g^4+100*s^4*g^6+100*s^6+400*s^6*g^2+100*s^6*g^4+25*s^8+25*s^8*g^2+s^10

def originalCubicQuinticMinEnergy (s g : ℝ) : ℝ :=
  min 1 (s^2) * (25*(1+16*g^2+36*g^4+16*g^6+g^8+16*s^2+144*s^2*g^2+144*s^2*g^4+16*s^2*g^6+36*s^4+144*s^4*g^2+36*s^4*g^4+16*s^6+16*s^6*g^2+s^8))

theorem originalCubicQuintic_norm_pos (s g : ℝ) :
    0 < originalCubicQuinticNormSq s g := by
  unfold originalCubicQuinticNormSq
  positivity

theorem originalCubicQuintic_energy_pos {s : ℝ} (hs : s ≠ 0) (g : ℝ) :
    0 < originalCubicQuinticMinEnergy s g := by
  exact mul_pos (lt_min zero_lt_one (sq_pos_of_ne_zero hs)) (by positivity)

theorem originalCubicQuintic_zero_data (s : ℝ) :
    originalCubicQuinticNormSq s 0 = originalHyperbolicQuinticNormSq s ∧
    originalCubicQuinticMinEnergy s 0 =
      min (originalHyperbolicQuinticXEnergy s) (originalHyperbolicQuinticYEnergy s) := by
  constructor
  · simp [originalCubicQuinticNormSq,originalHyperbolicQuinticNormSq]
    <;> ring
  · rw [originalCubicQuinticMinEnergy,min_mul_of_nonneg _ _ (by positivity),one_mul]
    congr 1 <;> simp [originalHyperbolicQuinticXEnergy,originalHyperbolicQuinticYEnergy] <;> ring

set_option maxHeartbeats 2000000 in
theorem originalCubicQuintic_g_ratio_factor (s g h : ℝ) :
    originalCubicQuinticNormSq s g * originalCubicQuinticMinEnergy s h -
      originalCubicQuinticNormSq s h * originalCubicQuinticMinEnergy s g =
    min 1 (s^2)*25*(g^2-h^2)*
      (9+64*h^2+84*h^4+24*h^6+1*h^8+64*g^2+784*g^2*h^2+1224*g^2*h^4+376*g^2*h^6+16*g^2*h^8+84*g^4+1224*g^4*h^2+2376*g^4*h^4+816*g^4*h^6+36*g^4*h^8+24*g^6+376*g^6*h^2+816*g^6*h^4+336*g^6*h^6+16*g^6*h^8+1*g^8+16*g^8*h^2+36*g^8*h^4+16*g^8*h^6+1*g^8*h^8+256*s^2+1456*s^2*h^2+1584*s^2*h^4+400*s^2*h^6+16*s^2*h^8+1456*s^2*g^2+12384*s^2*g^2*h^2+14400*s^2*g^2*h^4+3616*s^2*g^2*h^6+144*s^2*g^2*h^8+1584*s^2*g^4+14400*s^2*g^4*h^2+16416*s^2*g^4*h^4+3744*s^2*g^4*h^6+144*s^2*g^4*h^8+400*s^2*g^6+3616*s^2*g^6*h^2+3744*s^2*g^6*h^4+544*s^2*g^6*h^6+16*s^2*g^6*h^8+16*s^2*g^8+144*s^2*g^8*h^2+144*s^2*g^8*h^4+16*s^2*g^8*h^6+2856*s^4+11664*s^4*h^2+8100*s^4*h^4+1200*s^4*h^6+36*s^4*h^8+11664*s^4*g^2+75600*s^4*g^2*h^2+54000*s^4*g^2*h^4+6336*s^4*g^2*h^6+144*s^4*g^2*h^8+8100*s^4*g^4+54000*s^4*g^4*h^2+42336*s^4*g^4*h^4+3744*s^4*g^4*h^6+36*s^4*g^4*h^8+1200*s^4*g^6+6336*s^4*g^6*h^2+3744*s^4*g^6*h^4+336*s^4*g^6*h^6+36*s^4*g^8+144*s^4*g^8*h^2+36*s^4*g^8*h^4+9984*s^6+29600*s^6*h^2+14400*s^6*h^4+1200*s^6*h^6+16*s^6*h^8+29600*s^6*g^2+118400*s^6*g^2*h^2+54000*s^6*g^2*h^4+3616*s^6*g^2*h^6+16*s^6*g^2*h^8+14400*s^6*g^4+54000*s^6*g^4*h^2+16416*s^6*g^4*h^4+816*s^6*g^4*h^6+1200*s^6*g^6+3616*s^6*g^6*h^2+816*s^6*g^6*h^4+16*s^6*g^8+16*s^6*g^8*h^2+15650*s^8+29600*s^8*h^2+8100*s^8*h^4+400*s^8*h^6+1*s^8*h^8+29600*s^8*g^2+75600*s^8*g^2*h^2+14400*s^8*g^2*h^4+376*s^8*g^2*h^6+8100*s^8*g^4+14400*s^8*g^4*h^2+2376*s^8*g^4*h^4+400*s^8*g^6+376*s^8*g^6*h^2+1*s^8*g^8+9984*s^10+11664*s^10*h^2+1584*s^10*h^4+24*s^10*h^6+11664*s^10*g^2+12384*s^10*g^2*h^2+1224*s^10*g^2*h^4+1584*s^10*g^4+1224*s^10*g^4*h^2+24*s^10*g^6+2856*s^12+1456*s^12*h^2+84*s^12*h^4+1456*s^12*g^2+784*s^12*g^2*h^2+84*s^12*g^4+256*s^14+64*s^14*h^2+64*s^14*g^2+9*s^16) := by
  unfold originalCubicQuinticNormSq originalCubicQuinticMinEnergy
  ring

set_option maxHeartbeats 2000000 in
theorem originalCubicQuintic_g_ratio_improves {s g h : ℝ} (hs : s ≠ 0)
    (hh : h^2 < g^2) :
    originalCubicQuinticNormSq s h * originalCubicQuinticMinEnergy s g <
      originalCubicQuinticNormSq s g * originalCubicQuinticMinEnergy s h := by
  have hp : 0 < min 1 (s^2)*25*(g^2-h^2)*
      (9+64*h^2+84*h^4+24*h^6+1*h^8+64*g^2+784*g^2*h^2+1224*g^2*h^4+376*g^2*h^6+16*g^2*h^8+84*g^4+1224*g^4*h^2+2376*g^4*h^4+816*g^4*h^6+36*g^4*h^8+24*g^6+376*g^6*h^2+816*g^6*h^4+336*g^6*h^6+16*g^6*h^8+1*g^8+16*g^8*h^2+36*g^8*h^4+16*g^8*h^6+1*g^8*h^8+256*s^2+1456*s^2*h^2+1584*s^2*h^4+400*s^2*h^6+16*s^2*h^8+1456*s^2*g^2+12384*s^2*g^2*h^2+14400*s^2*g^2*h^4+3616*s^2*g^2*h^6+144*s^2*g^2*h^8+1584*s^2*g^4+14400*s^2*g^4*h^2+16416*s^2*g^4*h^4+3744*s^2*g^4*h^6+144*s^2*g^4*h^8+400*s^2*g^6+3616*s^2*g^6*h^2+3744*s^2*g^6*h^4+544*s^2*g^6*h^6+16*s^2*g^6*h^8+16*s^2*g^8+144*s^2*g^8*h^2+144*s^2*g^8*h^4+16*s^2*g^8*h^6+2856*s^4+11664*s^4*h^2+8100*s^4*h^4+1200*s^4*h^6+36*s^4*h^8+11664*s^4*g^2+75600*s^4*g^2*h^2+54000*s^4*g^2*h^4+6336*s^4*g^2*h^6+144*s^4*g^2*h^8+8100*s^4*g^4+54000*s^4*g^4*h^2+42336*s^4*g^4*h^4+3744*s^4*g^4*h^6+36*s^4*g^4*h^8+1200*s^4*g^6+6336*s^4*g^6*h^2+3744*s^4*g^6*h^4+336*s^4*g^6*h^6+36*s^4*g^8+144*s^4*g^8*h^2+36*s^4*g^8*h^4+9984*s^6+29600*s^6*h^2+14400*s^6*h^4+1200*s^6*h^6+16*s^6*h^8+29600*s^6*g^2+118400*s^6*g^2*h^2+54000*s^6*g^2*h^4+3616*s^6*g^2*h^6+16*s^6*g^2*h^8+14400*s^6*g^4+54000*s^6*g^4*h^2+16416*s^6*g^4*h^4+816*s^6*g^4*h^6+1200*s^6*g^6+3616*s^6*g^6*h^2+816*s^6*g^6*h^4+16*s^6*g^8+16*s^6*g^8*h^2+15650*s^8+29600*s^8*h^2+8100*s^8*h^4+400*s^8*h^6+1*s^8*h^8+29600*s^8*g^2+75600*s^8*g^2*h^2+14400*s^8*g^2*h^4+376*s^8*g^2*h^6+8100*s^8*g^4+14400*s^8*g^4*h^2+2376*s^8*g^4*h^4+400*s^8*g^6+376*s^8*g^6*h^2+1*s^8*g^8+9984*s^10+11664*s^10*h^2+1584*s^10*h^4+24*s^10*h^6+11664*s^10*g^2+12384*s^10*g^2*h^2+1224*s^10*g^2*h^4+1584*s^10*g^4+1224*s^10*g^4*h^2+24*s^10*g^6+2856*s^12+1456*s^12*h^2+84*s^12*h^4+1456*s^12*g^2+784*s^12*g^2*h^2+84*s^12*g^4+256*s^14+64*s^14*h^2+64*s^14*g^2+9*s^16) := by
    exact mul_pos (mul_pos (mul_pos (lt_min zero_lt_one (sq_pos_of_ne_zero hs)) (by norm_num))
      (sub_pos.mpr hh)) (by positivity)
  rw [← originalCubicQuintic_g_ratio_factor] at hp
  exact sub_pos.mp hp

theorem originalCubicQuintic_g_ratio_improvement {s g A : ℝ} (hs : s ≠ 0) (hg : g ≠ 0)
    (he : originalCubicQuinticNormSq s g = A^4*originalCubicQuinticMinEnergy s g) :
    ∃ᶠ b : ℝ in 𝓝 1, 0 < b ∧ b < 1 ∧
      originalCubicQuinticNormSq s (b*g) < A^4*originalCubicQuinticMinEnergy s (b*g) := by
  apply ((frequently_lt_nhds (1 : ℝ)).and_eventually (Ioi_mem_nhds zero_lt_one)).mono
  rintro b ⟨hb1,hb⟩
  refine ⟨hb,hb1,?_⟩
  have hb2 : b^2 < 1 := by nlinarith
  have hh : (b*g)^2 < g^2 := by
    nlinarith [mul_pos (sub_pos.mpr hb2) (sq_pos_of_ne_zero hg)]
  apply (mul_lt_mul_right (originalCubicQuintic_energy_pos hs g)).mp
  calc
    originalCubicQuinticNormSq s (b*g)*originalCubicQuinticMinEnergy s g <
      originalCubicQuinticNormSq s g*originalCubicQuinticMinEnergy s (b*g) :=
        originalCubicQuintic_g_ratio_improves hs hh
    _ = (A^4*originalCubicQuinticMinEnergy s (b*g))*originalCubicQuinticMinEnergy s g := by
      rw [he];ring

end PaperI
