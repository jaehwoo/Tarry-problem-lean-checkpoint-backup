import PaperILean.OriginalDGaugeBox

/-! Original-coordinate restoration and bounded comparisons for the fixed-a
sampling nets in I1593, cases 15 and 16. The displayed gauged box is the input;
no ODE integration, sampling net or covering bound is assumed. -/

noncomputable section
namespace PaperI.FixedABoxComparisons

def boxWeight (H U W : ℝ) : Fin 6 → ℝ :=
  ![H,H*U,H*(H+U*W),U,H+U*W,W]

def BoxBound (q : Fin 6 → ℝ) (K H U W : ℝ) : Prop :=
  ∀ i, |q i| ≤ K * boxWeight H U W i

def rawBoxWeight (H u w : ℝ) : Fin 6 → ℝ :=
  ![H,H*u,H^2+H*u*w,u,H+u*w,w]

def RawBoxBound (q : Fin 6 → ℝ) (K H u w : ℝ) : Prop :=
  ∀ i, |q i| ≤ K * rawBoxWeight H u w i

def gaugeFrame (beta tau : ℝ) : Fin 6 → ℝ := ![0,0,0,beta,tau,0]

def gaugeBack (q : Fin 6 → ℝ) (beta0 tau0 beta1 tau1 : ℝ) : Fin 6 → ℝ :=
  originalUpperAffineComp
    (originalUpperAffineComp (originalUpperAffineInv (gaugeFrame beta0 tau0)) q)
    (gaugeFrame beta1 tau1)

def restoredPoint (q : Fin 6 → ℝ) (beta0 tau0 beta1 tau1 : ℝ)
    (l r : Fin 6 → ℝ) : Fin 6 → ℝ :=
  originalUpperAffineComp
    (originalUpperAffineComp l (gaugeBack q beta0 tau0 beta1 tau1)) r

theorem gaugeFrame_inv (beta tau : ℝ) :
    originalUpperAffineInv (gaugeFrame beta tau) = gaugeFrame (-beta) (-tau) := by
  ext i
  fin_cases i <;> simp [gaugeFrame, originalUpperAffineInv]

theorem gaugeBack_coordinates (q : Fin 6 → ℝ) (beta0 tau0 beta1 tau1 : ℝ) :
    gaugeBack q beta0 tau0 beta1 tau1 =
      ![q 0,q 1+q 0*beta1,q 2+q 0*tau1,q 3+beta1-beta0,
        q 4+tau1-tau0-beta0*q 5,q 5] := by
  ext i
  fin_cases i <;>
    simp [gaugeBack, gaugeFrame, originalUpperAffineComp, originalUpperAffineInv] <;> ring

theorem boxWeight_ge_one (H U W : ℝ) (hH : 1 ≤ H) (hU : 1 ≤ U)
    (hW : 1 ≤ W) (i : Fin 6) : 1 ≤ boxWeight H U W i := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hUW : 1 ≤ U*W := one_le_mul_of_one_le_of_one_le hU hW
  have hE : 1 ≤ H+U*W := by linarith
  have hHU := one_le_mul_of_one_le_of_one_le hH hU
  have hHE := one_le_mul_of_one_le_of_one_le hH hE
  fin_cases i <;> simp only [boxWeight, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val] <;> assumption

theorem boxBound_mono {q : Fin 6 → ℝ} {K L H U W : ℝ}
    (hH : 0 ≤ H) (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hK : K ≤ L) (hq : BoxBound q K H U W) : BoxBound q L H U W := by
  intro i
  apply (hq i).trans
  apply mul_le_mul_of_nonneg_right hK
  fin_cases i <;> simp [boxWeight] <;> positivity

theorem raw_to_max_box (q : Fin 6 → ℝ) (K H u w : ℝ)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hq : RawBoxBound q K H u w) :
    BoxBound q K H (max 1 u) (max 1 w) := by
  have hU0 : 0 ≤ max 1 u := le_trans zero_le_one (le_max_left _ _)
  have hp : u*w ≤ max 1 u * max 1 w :=
    mul_le_mul (le_max_right _ _) (le_max_right _ _) hw hU0
  have hwidth (i : Fin 6) : rawBoxWeight H u w i ≤
      boxWeight H (max 1 u) (max 1 w) i := by
    fin_cases i
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hH
    · change H^2+H*u*w ≤ H*(H+max 1 u*max 1 w)
      have hh := mul_le_mul_of_nonneg_left hp hH
      nlinarith only [hh]
    · exact le_max_right _ _
    · exact add_le_add_left hp H
    · exact le_max_right _ _
  intro i
  exact (hq i).trans (mul_le_mul_of_nonneg_left (hwidth i) hK)

private theorem boxBound_mul_bounded_raw (q r : Fin 6 → ℝ) (K R H U W : ℝ)
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
  have hE0 : 0 ≤ H+U*W := by positivity
  have hEU : U ≤ H+U*W := by
    have hu := le_mul_of_one_le_right hU0 hW
    linarith
  have hEW : W ≤ H+U*W := by
    have hw := le_mul_of_one_le_left hW0 hU
    linarith
  have hw1 (i : Fin 6) : 1 ≤ boxWeight H U W i :=
    boxWeight_ge_one H U W hH hU hW i
  have hw0 (i : Fin 6) : 0 ≤ boxWeight H U W i := le_trans zero_le_one (hw1 i)
  have h01 : boxWeight H U W 0 ≤ boxWeight H U W 1 := by
    change H ≤ H*U
    exact le_mul_of_one_le_right hH0 hU
  have h12 : boxWeight H U W 1 ≤ boxWeight H U W 2 := by
    change H*U ≤ H*(H+U*W)
    exact mul_le_mul_of_nonneg_left hEU hH0
  have h02 : boxWeight H U W 0 ≤ boxWeight H U W 2 := le_trans h01 h12
  have h31 : boxWeight H U W 3 ≤ boxWeight H U W 1 := by
    change U ≤ H*U
    exact le_mul_of_one_le_left hU0 hH
  have h34 : boxWeight H U W 3 ≤ boxWeight H U W 4 := hEU
  have h42 : boxWeight H U W 4 ≤ boxWeight H U W 2 := by
    change H+U*W ≤ H*(H+U*W)
    exact le_mul_of_one_le_left hE0 hH
  have h54 : boxWeight H U W 5 ≤ boxWeight H U W 4 := hEW
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


theorem boxBound_mul_bounded (q r : Fin 6 → ℝ) (K B H U W : ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K) (hB : 1 ≤ B)
    (hq : BoxBound q K H U W) (hr : ∀ i, |r i| ≤ B) :
    BoxBound (originalUpperAffineComp q r) (4*K*B) H U W ∧
      BoxBound (originalUpperAffineComp r q) (4*K*B) H U W := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hc : K+B+2*K*B ≤ 4*K*B := by
    have h1 := le_mul_of_one_le_right hK0 hB
    have h2 := le_mul_of_one_le_left hB0 hK
    nlinarith only [h1,h2]
  have hh := boxBound_mul_bounded_raw q r K B H U W hH hU hW hK0 hB0 hq hr
  exact ⟨boxBound_mono (le_trans zero_le_one hH) (le_trans zero_le_one hU)
    (le_trans zero_le_one hW) hc hh.1,
    boxBound_mono (le_trans zero_le_one hH) (le_trans zero_le_one hU)
    (le_trans zero_le_one hW) hc hh.2⟩

theorem gaugeFrame_bound (beta tau B : ℝ) (hB : 0 ≤ B)
    (hb : |beta| ≤ B) (ht : |tau| ≤ B) :
    (∀ i, |gaugeFrame beta tau i| ≤ B) ∧
      ∀ i, |originalUpperAffineInv (gaugeFrame beta tau) i| ≤ B := by
  constructor
  · intro i
    fin_cases i <;> simp [gaugeFrame] <;> assumption
  · rw [gaugeFrame_inv]
    intro i
    fin_cases i <;> simp [gaugeFrame] <;> assumption

/-- Both the endpoint gauge pair and the arbitrary later comparison pair are retained. -/
theorem restored_point_box (q l r : Fin 6 → ℝ)
    (K B H U W beta0 tau0 beta1 tau1 : ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K) (hB : 1 ≤ B)
    (hq : BoxBound q K H U W)
    (hb0 : |beta0| ≤ B) (ht0 : |tau0| ≤ B)
    (hb1 : |beta1| ≤ B) (ht1 : |tau1| ≤ B)
    (hl : ∀ i, |l i| ≤ B) (hr : ∀ i, |r i| ≤ B) :
    BoxBound (restoredPoint q beta0 tau0 beta1 tau1 l r) (256*K*B^4) H U W := by
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hS0 := (gaugeFrame_bound beta0 tau0 B hB0 hb0 ht0).2
  have hS1 := (gaugeFrame_bound beta1 tau1 B hB0 hb1 ht1).1
  have step (M : ℝ) (hM : 1 ≤ M) : 1 ≤ 4*M*B :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) hM) hB
  have h0 := (boxBound_mul_bounded q (originalUpperAffineInv (gaugeFrame beta0 tau0))
    K B H U W hH hU hW hK hB hq hS0).2
  have h1 := (boxBound_mul_bounded _ (gaugeFrame beta1 tau1)
    (4*K*B) B H U W hH hU hW (step K hK) hB h0 hS1).1
  have h2 := (boxBound_mul_bounded _ l
    (4*(4*K*B)*B) B H U W hH hU hW (step _ (step K hK)) hB h1 hl).2
  have h3 := (boxBound_mul_bounded _ r
    (4*(4*(4*K*B)*B)*B) B H U W hH hU hW
      (step _ (step _ (step K hK))) hB h2 hr).1
  have heq : 4*(4*(4*(4*K*B)*B)*B)*B = 256*K*B^4 := by ring
  rw [heq] at h3
  exact h3

theorem restored_conditioning_power (P C : ℝ) (hP : 2 ≤ P) :
    256*(P^C)*(P^C)^4 ≤ P^(5*C+8) := by
  have hP0 : 0 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have h256 : (256 : ℝ) ≤ P^8 := by
    calc
      256 = (2 : ℝ)^8 := by norm_num
      _ ≤ P^8 := pow_le_pow_left₀ (by norm_num) hP 8
  have heq : P^(5*C+8) = (P^C)^5 * P^8 := by
    rw [Real.rpow_add hPpos, show (5:ℝ)*C=C*5 by ring, Real.rpow_mul hP0]
    exact congrArg₂ (fun x y : ℝ => x*y)
      (Real.rpow_natCast (P^C) 5) (Real.rpow_natCast P 8)
  rw [heq]
  have hh := mul_le_mul_of_nonneg_right h256 (show 0 ≤ (P^C)^5 by positivity)
  nlinarith only [hh]

/-- The source raw box, actual endpoint gauges and both bounded comparisons
imply the original box used by the fixed-a net. No cover is assumed. -/
theorem restored_point_box_power (q l r : Fin 6 → ℝ)
    (P C H u w beta0 tau0 beta1 tau1 : ℝ)
    (hP : 2 ≤ P) (hC : 0 ≤ C) (hH : 1 ≤ H) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hq : RawBoxBound q (P^C) H u w)
    (hb0 : |beta0| ≤ P^C) (ht0 : |tau0| ≤ P^C)
    (hb1 : |beta1| ≤ P^C) (ht1 : |tau1| ≤ P^C)
    (hl : ∀ i, |l i| ≤ P^C) (hr : ∀ i, |r i| ≤ P^C) :
    BoxBound (restoredPoint q beta0 tau0 beta1 tau1 l r)
      (P^(5*C+8)) H (max 1 u) (max 1 w) := by
  have hB : 1 ≤ P^C := Real.one_le_rpow (by linarith) hC
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hU : 1 ≤ max 1 u := le_max_left _ _
  have hW : 1 ≤ max 1 w := le_max_left _ _
  have hqmax := raw_to_max_box q (P^C) H u w (le_trans zero_le_one hB) hH0 hu hw hq
  have hh := restored_point_box q l r (P^C) (P^C) H (max 1 u) (max 1 w)
    beta0 tau0 beta1 tau1 hH hU hW hB hB hqmax hb0 ht0 hb1 ht1 hl hr
  exact boxBound_mono hH0 (le_trans zero_le_one hU) (le_trans zero_le_one hW)
    (restored_conditioning_power P C hP) hh

end PaperI.FixedABoxComparisons
