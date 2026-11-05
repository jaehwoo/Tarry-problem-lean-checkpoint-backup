import PaperILean.OriginalDGaugeWidths

noncomputable section
namespace PaperI.OriginalDGaugeBox
open OriginalDGauge OriginalDGaugeMultiplyback

def boxWeight (H U W : ℝ) : Fin 6 → ℝ := ![U,H*U,H*U*W,H,H*W,W]
def BoxBound (q : Fin 6 → ℝ) (K H U W : ℝ) : Prop :=
  ∀ i, |q i| ≤ K * boxWeight H U W i

theorem multiplyback_box_of_bounds (q : Fin 6 → ℝ)
    (H u w M B U W beta0 beta eta0 eta : ℝ)
    (hH : 0 ≤ H) (hu : 0 ≤ u) (hw : 0 ≤ w) (hM : 0 ≤ M)
    (hB : 1 ≤ B) (hU : 1 ≤ U) (hW : 1 ≤ W) (huU : u ≤ U) (hwW : w ≤ W)
    (hq : |q 0| ≤ u ∧ |q 1| ≤ H*u ∧ |q 2| ≤ H*(M+u*w) ∧
      |q 3| ≤ H ∧ |q 4| ≤ H*w ∧ |q 5| ≤ w)
    (hb0 : |beta0| ≤ B) (hb : |beta| ≤ B)
    (he0 : |eta0| ≤ B) (he : |eta| ≤ B) :
    BoxBound (multiplyback q beta0 beta eta0 eta) (M+(B+1)^2) H U W ∧
      |beta0*q 4| ≤ B*H*W ∧ B*H*W ≤ B*H*U*W := by
  rcases hq with ⟨ha,hbq,hcq,hd,heq,hf⟩
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hW0 : 0 ≤ W := le_trans (by norm_num) hW
  have hUW : 1 ≤ U*W := one_le_mul_of_one_le_of_one_le hU hW
  have huUW : u ≤ U*W := huU.trans (le_mul_of_one_le_right hU0 hW)
  have hwUW : w ≤ U*W := hwW.trans (le_mul_of_one_le_left hW0 hU)
  have huwUW : u*w ≤ U*W := mul_le_mul huU hwW hw hU0
  have hK1 : 1 ≤ M+(B+1)^2 := by nlinarith only [hM,hB,sq_nonneg B]
  have hKa : 1+2*B ≤ M+(B+1)^2 := by nlinarith only [hM,hB,sq_nonneg B]
  have hKe : 1+B ≤ M+(B+1)^2 := by nlinarith only [hM,hB,sq_nonneg B]
  have hbe : |beta0*q 4| ≤ B*(H*w) := by
    rw [abs_mul]
    exact mul_le_mul hb0 heq (abs_nonneg _) hB0
  have hbd : |beta0*q 3| ≤ B*H := by
    rw [abs_mul]
    exact mul_le_mul hb0 hd (abs_nonneg _) hB0
  have hbt : |q 1+beta0*q 3| ≤ H*u+B*H :=
    (abs_add _ _).trans (add_le_add hbq hbd)
  have hbte : |(q 1+beta0*q 3)*eta| ≤ (H*u+B*H)*B := by
    rw [abs_mul]
    exact mul_le_mul hbt he (abs_nonneg _) (by positivity)
  have hde : |q 3*eta| ≤ H*B := by
    rw [abs_mul]
    exact mul_le_mul hd he (abs_nonneg _) hH
  have hExtra : |beta0*q 4| ≤ B*H*W := by
    calc
      _ ≤ B*(H*w) := hbe
      _ ≤ B*(H*W) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hwW hH) hB0
      _ = _ := by ring
  refine ⟨?_, hExtra, ?_⟩
  · intro i
    fin_cases i
    · change |q 0+beta0-beta| ≤ (M+(B+1)^2)*U
      calc
        _ ≤ |q 0|+|beta0|+|beta| :=
          (abs_sub _ _).trans (add_le_add_right (abs_add _ _) _)
        _ ≤ u+B+B := by gcongr
        _ ≤ (1+2*B)*U := by nlinarith only [huU, mul_nonneg hB0 (sub_nonneg.mpr hU)]
        _ ≤ _ := mul_le_mul_of_nonneg_right hKa hU0
    · change |q 1+beta0*q 3| ≤ (M+(B+1)^2)*(H*U)
      calc
        _ ≤ H*u+B*H := hbt
        _ ≤ (1+B)*(H*U) := by nlinarith only [mul_nonneg hH (sub_nonneg.mpr huU), mul_nonneg (mul_nonneg hB0 hH) (sub_nonneg.mpr hU)]
        _ ≤ _ := mul_le_mul_of_nonneg_right hKe (mul_nonneg hH hU0)
    · change |q 2+beta0*q 4+(q 1+beta0*q 3)*eta| ≤
        (M+(B+1)^2)*(H*U*W)
      have hsum : M+u*w+B*w+B*u+B^2 ≤ (M+(B+1)^2)*(U*W) := by
        have h1 := mul_le_mul_of_nonneg_left hUW hM
        have h2 := mul_le_mul_of_nonneg_left hwUW hB0
        have h3 := mul_le_mul_of_nonneg_left huUW hB0
        have h4 := mul_le_mul_of_nonneg_left hUW (sq_nonneg B)
        nlinarith only [h1,h2,h3,h4,huwUW]
      calc
        _ ≤ |q 2|+|beta0*q 4|+|(q 1+beta0*q 3)*eta| :=
          (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
        _ ≤ H*(M+u*w)+B*(H*w)+(H*u+B*H)*B := by gcongr
        _ = H*(M+u*w+B*w+B*u+B^2) := by ring
        _ ≤ H*((M+(B+1)^2)*(U*W)) := mul_le_mul_of_nonneg_left hsum hH
        _ = _ := by ring
    · change |q 3| ≤ (M+(B+1)^2)*H
      exact hd.trans (le_mul_of_one_le_left hH hK1)
    · change |q 4+q 3*eta| ≤ (M+(B+1)^2)*(H*W)
      calc
        _ ≤ |q 4|+|q 3*eta| := abs_add _ _
        _ ≤ H*w+H*B := add_le_add heq hde
        _ ≤ (1+B)*(H*W) := by nlinarith only [mul_nonneg hH (sub_nonneg.mpr hwW), mul_nonneg (mul_nonneg hB0 hH) (sub_nonneg.mpr hW)]
        _ ≤ _ := mul_le_mul_of_nonneg_right hKe (mul_nonneg hH hW0)
    · change |q 5+eta-eta0| ≤ (M+(B+1)^2)*W
      calc
        _ ≤ |q 5|+|eta|+|eta0| :=
          (abs_sub _ _).trans (add_le_add_right (abs_add _ _) _)
        _ ≤ w+B+B := by gcongr
        _ ≤ (1+2*B)*W := by nlinarith only [hwW, mul_nonneg hB0 (sub_nonneg.mpr hW)]
        _ ≤ _ := mul_le_mul_of_nonneg_right hKa hW0
  · have hh := mul_le_mul_of_nonneg_left hU (mul_nonneg hB0 hH)
    have hh' := mul_le_mul_of_nonneg_right hh hW0
    simpa only [mul_one] using hh'

theorem boxBound_mono {q : Fin 6 → ℝ} {K L H U W : ℝ}
    (hH : 0 ≤ H) (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hK : K ≤ L) (hq : BoxBound q K H U W) : BoxBound q L H U W := by
  intro i
  apply (hq i).trans
  apply mul_le_mul_of_nonneg_right hK
  fin_cases i <;> simp [boxWeight] <;> positivity

theorem original_box_conditioning_constant (P C : ℝ) (hP : 2 ≤ P)
    (hB : 1 ≤ P^C) :
    (P^C+(P^C)^2)+((P^C)+1)^2 ≤ P^(2*C+3) := by
  have hP0 : 0 ≤ P := by linarith
  have heq : P^(2*C+3) = (P^C)^2 * P^3 := by
    rw [Real.rpow_add (by linarith : 0 < P),
      show (2:ℝ)*C=C*2 by ring, Real.rpow_mul hP0,
      Real.rpow_two]
    exact congrArg _ (Real.rpow_natCast P 3)
  rw [heq]
  have hB0 : 0 ≤ P^C := le_trans (by norm_num) hB
  have hcube : 8 ≤ P^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hP) (sq_nonneg P)]
  have hp := mul_le_mul_of_nonneg_right hcube (sq_nonneg (P^C))
  nlinarith [sq_nonneg (P^C-1)]

theorem boxBound_mul_bounded (q r : Fin 6 → ℝ) (K R H U W : ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hq : BoxBound q K H U W) (hr : ∀ i, |r i| ≤ R) :
    BoxBound (originalUpperAffineComp q r) (K+R+2*K*R) H U W ∧
      BoxBound (originalUpperAffineComp r q) (K+R+2*K*R) H U W := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hU0 : 0 ≤ U := le_trans zero_le_one hU
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hHU : 1 ≤ H*U := by
    calc
      1 = 1*1 := by ring
      _ ≤ H*U := mul_le_mul hH hU zero_le_one hH0
  have hHW : 1 ≤ H*W := by
    calc
      1 = 1*1 := by ring
      _ ≤ H*W := mul_le_mul hH hW zero_le_one hH0
  have hHUW : 1 ≤ H*U*W := by
    calc
      1 = 1*1 := by ring
      _ ≤ H*U*W := mul_le_mul hHU hW zero_le_one (by positivity)
  have hw1 (i : Fin 6) : 1 ≤ boxWeight H U W i := by
    fin_cases i <;> simp only [boxWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] <;> assumption
  have hw0 (i : Fin 6) : 0 ≤ boxWeight H U W i := le_trans zero_le_one (hw1 i)
  have h01 : boxWeight H U W 0 ≤ boxWeight H U W 1 := by
    change U ≤ H*U
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hH hU0
  have h12 : boxWeight H U W 1 ≤ boxWeight H U W 2 := by
    change H*U ≤ H*U*W
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hW (mul_nonneg hH0 hU0)
  have h02 : boxWeight H U W 0 ≤ boxWeight H U W 2 := le_trans h01 h12
  have h31 : boxWeight H U W 3 ≤ boxWeight H U W 1 := by
    change H ≤ H*U
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hU hH0
  have h34 : boxWeight H U W 3 ≤ boxWeight H U W 4 := by
    change H ≤ H*W
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hW hH0
  have h42 : boxWeight H U W 4 ≤ boxWeight H U W 2 := by
    change H*W ≤ H*U*W
    exact mul_le_mul_of_nonneg_right h31 hW0
  have h54 : boxWeight H U W 5 ≤ boxWeight H U W 4 := by
    change W ≤ H*W
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hH hW0
  have h52 : boxWeight H U W 5 ≤ boxWeight H U W 2 := le_trans h54 h42
  have hrw (i j : Fin 6) : |r i| ≤ R * boxWeight H U W j := by
    apply (hr i).trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw1 j) hR
  have hb (i : Fin 6) : |q i+r i| ≤ (K+R)*boxWeight H U W i := by
    calc
      _ ≤ |q i|+|r i| := abs_add _ _
      _ ≤ K*boxWeight H U W i+R*boxWeight H U W i := add_le_add (hq i) (hrw i i)
      _ = _ := by ring
  have hm (i j k : Fin 6) (h : boxWeight H U W i ≤ boxWeight H U W k) :
      |q i*r j| ≤ K*R*boxWeight H U W k := by
    calc
      _ = |q i| * |r j| := abs_mul _ _
      _ ≤ (K*boxWeight H U W k)*R :=
        mul_le_mul ((hq i).trans (mul_le_mul_of_nonneg_left h hK)) (hr j)
          (abs_nonneg _) (mul_nonneg hK (hw0 k))
      _ = _ := by ring
  have hp (i : Fin 6) : 0 ≤ K*R*boxWeight H U W i :=
    mul_nonneg (mul_nonneg hK hR) (hw0 i)
  have finish (x y : Fin 6 → ℝ)
      (hbxy : ∀ i, |x i+y i| ≤ (K+R)*boxWeight H U W i)
      (h013 : |x 0*y 3| ≤ K*R*boxWeight H U W 1)
      (h024 : |x 0*y 4| ≤ K*R*boxWeight H U W 2)
      (h125 : |x 1*y 5| ≤ K*R*boxWeight H U W 2)
      (h345 : |x 3*y 5| ≤ K*R*boxWeight H U W 4) :
      BoxBound (originalUpperAffineComp x y) (K+R+2*K*R) H U W := by
    intro i
    fin_cases i
    · change |x 0+y 0| ≤ (K+R+2*K*R)*boxWeight H U W 0
      nlinarith only [hbxy 0, hp 0]
    · change |x 1+y 1+x 0*y 3| ≤ (K+R+2*K*R)*boxWeight H U W 1
      have hh := (abs_add _ _).trans (add_le_add (hbxy 1) h013)
      nlinarith only [hh, hp 1]
    · change |x 2+y 2+x 0*y 4+x 1*y 5| ≤ (K+R+2*K*R)*boxWeight H U W 2
      have hh := (abs_add _ _).trans
        (add_le_add ((abs_add _ _).trans (add_le_add (hbxy 2) h024)) h125)
      nlinarith only [hh]
    · change |x 3+y 3| ≤ (K+R+2*K*R)*boxWeight H U W 3
      nlinarith only [hbxy 3, hp 3]
    · change |x 4+y 4+x 3*y 5| ≤ (K+R+2*K*R)*boxWeight H U W 4
      have hh := (abs_add _ _).trans (add_le_add (hbxy 4) h345)
      nlinarith only [hh, hp 4]
    · change |x 5+y 5| ≤ (K+R+2*K*R)*boxWeight H U W 5
      nlinarith only [hbxy 5, hp 5]
  constructor
  · exact finish q r hb (hm 0 3 1 h01) (hm 0 4 2 h02) (hm 1 5 2 h12) (hm 3 5 4 h34)
  · apply finish r q
    · intro i
      simpa only [add_comm] using hb i
    · simpa only [mul_comm] using hm 3 0 1 h31
    · simpa only [mul_comm] using hm 4 0 2 h42
    · simpa only [mul_comm] using hm 5 1 2 h52
    · simpa only [mul_comm] using hm 5 3 4 h54


open OriginalDGaugeWidths

/-- I1550[0,180): the actual original relative path lies in its stated
maximized box. The additional anchor term is explicitly absorbed. The
suprema are those of the actual corrected rates; no box bound is assumed. -/
theorem actual_d_gauge_original_box_bound
    (g v : ℝ → Fin 6 → ℝ) (beta eta dbeta deta : ℝ → ℝ)
    (S : Set ℝ) (t0 H P C Db De : ℝ)
    (hS : Convex ℝ S) (ht0 : t0 ∈ S) (hH : 1 ≤ H) (hP : 2 ≤ P)
    (hspan : ∀ t ∈ S, |t-t0| ≤ H)
    (hg : ∀ t ∈ S, HasDerivAt g (v t) t)
    (hb : ∀ t ∈ S, HasDerivAt beta (dbeta t) t)
    (he : ∀ t ∈ S, HasDerivAt eta (deta t) t)
    (hbeta : ∀ t ∈ S, beta t = originalAffineBodyCoordinates (g t) (v t) 1)
    (heta : ∀ t ∈ S, eta t = originalAffineBodyCoordinates (g t) (v t) 4)
    (hD : ∀ t ∈ S, originalAffineBodyCoordinates (g t) (v t) 3 = 1)
    (hbody : ∀ t ∈ S, ∀ i : Fin 6, |originalAffineBodyCoordinates (g t) (v t) i| ≤ P^C)
    (hdb : ∀ t ∈ S, |dbeta t| ≤ Db) (hde : ∀ t ∈ S, |deta t| ≤ De) :
    let U := max 1 (rawU H S g v dbeta)
    let W := max 1 (rawW H S g v deta)
    ∀ t ∈ S,
      BoxBound (originalUpperRelativeFrame (g t0) (g t)) (P^(2*C+3)) H U W ∧
      |beta t0 * gaugedRelativePath g beta eta t0 t 4| ≤ P^C*H*W ∧
      P^C*H*W ≤ P^C*H*U*W := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hB1 : 1 ≤ P^C := by simpa [hD t0 ht0] using hbody t0 ht0 3
  have hB0 : 0 ≤ P^C := zero_le_one.trans hB1
  obtain ⟨hu,hw,hraw⟩ := actual_d_gauge_raw_widths g v beta eta dbeta deta S t0 H (P^C) Db De
    hS ht0 hH0 hB0 hspan hg hb he hbeta heta hD hbody hdb hde
  have hb0 : |beta t0| ≤ P^C := by rw [hbeta t0 ht0]; exact hbody t0 ht0 1
  have he0 : |eta t0| ≤ P^C := by rw [heta t0 ht0]; exact hbody t0 ht0 4
  dsimp only
  intro t ht
  have hbt : |beta t| ≤ P^C := by rw [hbeta t ht]; exact hbody t ht 1
  have het : |eta t| ≤ P^C := by rw [heta t ht]; exact hbody t ht 4
  have hmul := multiplyback_box_of_bounds (gaugedRelativePath g beta eta t0 t)
    H (rawU H S g v dbeta) (rawW H S g v deta) (P^C+(P^C)^2) (P^C)
    (max 1 (rawU H S g v dbeta)) (max 1 (rawW H S g v deta))
    (beta t0) (beta t) (eta t0) (eta t)
    hH0 hu hw (add_nonneg hB0 (sq_nonneg _)) hB1
    (le_max_left _ _) (le_max_left _ _) (le_max_right _ _) (le_max_right _ _)
    (hraw t ht) hb0 hbt he0 het
  have hback : multiplyback (gaugedRelativePath g beta eta t0 t)
      (beta t0) (beta t) (eta t0) (eta t) = originalUpperRelativeFrame (g t0) (g t) :=
    gauged_relative_multiplyback (g t0) (g t) (beta t0) (beta t) (eta t0) (eta t)
  rw [hback] at hmul
  refine ⟨?_,hmul.2⟩
  exact boxBound_mono hH0 (zero_le_one.trans (le_max_left _ _))
    (zero_le_one.trans (le_max_left _ _)) (original_box_conditioning_constant P C hP hB1) hmul.1

theorem boxBound_two_bounded (q l r : Fin 6 → ℝ) (K R H U W : ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K) (hR : 1 ≤ R)
    (hq : BoxBound q K H U W) (hl : ∀ i, |l i| ≤ R) (hr : ∀ i, |r i| ≤ R) :
    BoxBound (originalUpperAffineComp (originalUpperAffineComp l q) r)
      (16*K*R^2) H U W := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hfour (L : ℝ) (hL : 1 ≤ L) : L+R+2*L*R ≤ 4*L*R := by
    have hL0 : 0 ≤ L := zero_le_one.trans hL
    have h1 := mul_le_mul_of_nonneg_left hR hL0
    have h2 := mul_le_mul_of_nonneg_right hL hR0
    nlinarith only [h1,h2]
  have hfour1 : 1 ≤ 4*K*R := by
    have h1 := one_le_mul_of_one_le_of_one_le hK hR
    nlinarith only [h1]
  have hleft := (boxBound_mul_bounded q l K R H U W hH hU hW hK0 hR0 hq hl).2
  have hleft4 := boxBound_mono hH0 hU0 hW0 (hfour K hK) hleft
  have hright := (boxBound_mul_bounded (originalUpperAffineComp l q) r (4*K*R) R
    H U W hH hU hW (zero_le_one.trans hfour1) hR0 hleft4 hr).1
  have hfinal := boxBound_mono hH0 hU0 hW0 (hfour (4*K*R) hfour1) hright
  convert hfinal using 1
  ring

theorem two_comparison_conditioning_constant (P C : ℝ) (hP : 2 ≤ P) :
    16*(P^(2*C+3))*(P^C)^2 ≤ P^(4*C+7) := by
  have hPpos : 0 < P := by linarith
  have heq : P^(4*C+7) = (P^(2*C+3))*(P^C)^2*P^4 := by
    rw [show 4*C+7 = ((2*C+3)+C*2)+4 by ring,
      Real.rpow_add hPpos, Real.rpow_add hPpos,
      Real.rpow_mul hPpos.le, Real.rpow_two]
    exact congrArg _ (Real.rpow_natCast P 4)
  rw [heq]
  have hP2 : 4 ≤ P^2 := by nlinarith only [hP,sq_nonneg (P-2)]
  have hP4 : 16 ≤ P^4 := by nlinarith only [hP2,sq_nonneg (P^2-4)]
  have hx : 0 ≤ (P^(2*C+3))*(P^C)^2 :=
    mul_nonneg (Real.rpow_nonneg hPpos.le _) (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_left hP4 hx
  nlinarith only [h]

/-- Complete source box restoration, with its bounded original comparisons.
This supplies no covering-number result: every conclusion is a coordinate
bound for the actual original relative path or its literal left/right product. -/
theorem actual_d_gauge_original_box_stage
    (g v : ℝ → Fin 6 → ℝ) (beta eta dbeta deta : ℝ → ℝ)
    (S : Set ℝ) (t0 H P C Db De : ℝ)
    (hS : Convex ℝ S) (ht0 : t0 ∈ S) (hH : 1 ≤ H) (hP : 2 ≤ P)
    (hspan : ∀ t ∈ S, |t-t0| ≤ H)
    (hg : ∀ t ∈ S, HasDerivAt g (v t) t)
    (hb : ∀ t ∈ S, HasDerivAt beta (dbeta t) t)
    (he : ∀ t ∈ S, HasDerivAt eta (deta t) t)
    (hbeta : ∀ t ∈ S, beta t = originalAffineBodyCoordinates (g t) (v t) 1)
    (heta : ∀ t ∈ S, eta t = originalAffineBodyCoordinates (g t) (v t) 4)
    (hD : ∀ t ∈ S, originalAffineBodyCoordinates (g t) (v t) 3 = 1)
    (hbody : ∀ t ∈ S, ∀ i : Fin 6, |originalAffineBodyCoordinates (g t) (v t) i| ≤ P^C)
    (hdb : ∀ t ∈ S, |dbeta t| ≤ Db) (hde : ∀ t ∈ S, |deta t| ≤ De) :
    let U := max 1 (rawU H S g v dbeta)
    let W := max 1 (rawW H S g v deta)
    ∀ t ∈ S,
      BoxBound (originalUpperRelativeFrame (g t0) (g t)) (P^(2*C+3)) H U W ∧
      |beta t0 * gaugedRelativePath g beta eta t0 t 4| ≤ P^C*H*W ∧
      P^C*H*W ≤ P^C*H*U*W ∧
      ∀ l r : Fin 6 → ℝ, (∀ i, |l i| ≤ P^C) → (∀ i, |r i| ≤ P^C) →
        BoxBound
          (originalUpperAffineComp (originalUpperAffineComp l
            (originalUpperRelativeFrame (g t0) (g t))) r)
          (P^(4*C+7)) H U W := by
  have hs := actual_d_gauge_original_box_bound g v beta eta dbeta deta S t0 H P C Db De
    hS ht0 hH hP hspan hg hb he hbeta heta hD hbody hdb hde
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hB1 : 1 ≤ P^C := by simpa [hD t0 ht0] using hbody t0 ht0 3
  have hKraw : 1 ≤ P^C+(P^C)^2+(P^C+1)^2 := by
    nlinarith only [hB1,sq_nonneg (P^C),sq_nonneg (P^C+1)]
  have hK1 : 1 ≤ P^(2*C+3) :=
    hKraw.trans (original_box_conditioning_constant P C hP hB1)
  dsimp only
  intro t ht
  have hh := hs t ht
  refine ⟨hh.1,hh.2.1,hh.2.2,?_⟩
  intro l r hl hr
  have hx := boxBound_two_bounded (originalUpperRelativeFrame (g t0) (g t)) l r
    (P^(2*C+3)) (P^C) H (max 1 (rawU H S g v dbeta)) (max 1 (rawW H S g v deta))
    hH (le_max_left _ _) (le_max_left _ _) hK1 hB1 hh.1 hl hr
  exact boxBound_mono hH0 (zero_le_one.trans (le_max_left _ _))
    (zero_le_one.trans (le_max_left _ _)) (two_comparison_conditioning_constant P C hP) hx

end PaperI.OriginalDGaugeBox
