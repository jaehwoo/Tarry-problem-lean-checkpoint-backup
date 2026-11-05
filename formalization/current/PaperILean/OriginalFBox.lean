import PaperILean.OriginalFGauge

/-! Necessary literal-coordinate box algebra for I1574 and I1576.
The two bounded comparisons act on the original coordinates in their actual
multiplication order. No covering-number assertion is made. -/

noncomputable section
namespace PaperI.OriginalFBox
open OriginalFGauge

def boxWeight (H u : ℝ) : Fin 6 → ℝ :=
  ![H,max H u,H*max H u,max 1 (u/H),max H u,H]

def BoxBound (q : Fin 6 → ℝ) (K H u : ℝ) : Prop :=
  ∀ i, |q i| ≤ K * boxWeight H u i

private theorem weight_ge_one (H u : ℝ) (hH : 1 ≤ H) :
    ∀ i, 1 ≤ boxWeight H u i := by
  have hB : 1 ≤ max H u := hH.trans (le_max_left _ _)
  have hHB : 1 ≤ H * max H u := one_le_mul_of_one_le_of_one_le hH hB
  intro i
  fin_cases i <;> simp only [boxWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  · exact hH
  · exact hB
  · exact hHB
  · exact le_max_left _ _
  · exact hB
  · exact hH

theorem boxBound_mono {q : Fin 6 → ℝ} {K L H u : ℝ}
    (hH : 1 ≤ H) (hu : 0 ≤ u) (hK : K ≤ L) (hq : BoxBound q K H u) :
    BoxBound q L H u := by
  intro i
  exact (hq i).trans (mul_le_mul_of_nonneg_right hK
    (zero_le_one.trans (weight_ge_one H u hH i)))

/-- The integrated raw f-chart widths imply the maximized source box. -/
theorem raw_bounds_to_box (q : Fin 6 → ℝ) (H u M : ℝ)
    (hH : 1 ≤ H) (hu : 0 ≤ u) (hM : 1 ≤ M)
    (hq : |q 0| ≤ H*M ∧ |q 1| ≤ M*(u+H) ∧
      |q 2| ≤ H*M*(u+H) ∧ |q 3| ≤ u/H ∧ |q 4| ≤ u ∧ |q 5| ≤ H) :
    BoxBound q (2*M) H u := by
  rcases hq with ⟨ha,hb,hc,hd,he,hf⟩
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hB0 : 0 ≤ max H u := hH0.trans (le_max_left _ _)
  have hsum : u+H ≤ 2*max H u := by linarith [le_max_left H u,le_max_right H u]
  have htwo : 1 ≤ 2*M := by linarith
  intro i
  fin_cases i
  · change |q 0| ≤ (2*M)*H
    nlinarith only [ha,mul_nonneg hH0 hM0]
  · change |q 1| ≤ (2*M)*max H u
    calc
      _ ≤ M*(u+H) := hb
      _ ≤ M*(2*max H u) := mul_le_mul_of_nonneg_left hsum hM0
      _ = _ := by ring
  · change |q 2| ≤ (2*M)*(H*max H u)
    calc
      _ ≤ H*M*(u+H) := hc
      _ ≤ H*M*(2*max H u) := mul_le_mul_of_nonneg_left hsum (mul_nonneg hH0 hM0)
      _ = _ := by ring
  · change |q 3| ≤ (2*M)*max 1 (u/H)
    exact (hd.trans (le_max_right _ _)).trans
      (le_mul_of_one_le_left (zero_le_one.trans (le_max_left _ _)) htwo)
  · change |q 4| ≤ (2*M)*max H u
    exact (he.trans (le_max_right _ _)).trans (le_mul_of_one_le_left hB0 htwo)
  · change |q 5| ≤ (2*M)*H
    exact hf.trans (le_mul_of_one_le_left hH0 htwo)

/-- One literal bounded factor on either side preserves the f-chart widths. -/
theorem boxBound_mul_bounded (q r : Fin 6 → ℝ) (K R H u : ℝ)
    (hH : 1 ≤ H) (hu : 0 ≤ u) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hq : BoxBound q K H u) (hr : ∀ i, |r i| ≤ R) :
    BoxBound (originalUpperAffineComp q r) (K+R+2*K*R) H u ∧
      BoxBound (originalUpperAffineComp r q) (K+R+2*K*R) H u := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hB0 : 0 ≤ max H u := hH0.trans (le_max_left _ _)
  have hB1 : 1 ≤ max H u := hH.trans (le_max_left _ _)
  have hw1 (i : Fin 6) : 1 ≤ boxWeight H u i := weight_ge_one H u hH i
  have hw0 (i : Fin 6) : 0 ≤ boxWeight H u i := zero_le_one.trans (hw1 i)
  have h01 : boxWeight H u 0 ≤ boxWeight H u 1 := by
    exact le_max_left H u
  have h12 : boxWeight H u 1 ≤ boxWeight H u 2 := by
    exact le_mul_of_one_le_left hB0 hH
  have h02 : boxWeight H u 0 ≤ boxWeight H u 2 := h01.trans h12
  have h31 : boxWeight H u 3 ≤ boxWeight H u 1 := by
    change max 1 (u/H) ≤ max H u
    refine max_le hB1 ((div_le_iff₀ hHpos).mpr ?_)
    exact (le_max_right H u).trans (le_mul_of_one_le_right hB0 hH)
  have h34 : boxWeight H u 3 ≤ boxWeight H u 4 := h31
  have h42 : boxWeight H u 4 ≤ boxWeight H u 2 := h12
  have h54 : boxWeight H u 5 ≤ boxWeight H u 4 := h01
  have h52 : boxWeight H u 5 ≤ boxWeight H u 2 := h02
  have hrw (i j : Fin 6) : |r i| ≤ R * boxWeight H u j := by
    apply (hr i).trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw1 j) hR
  have hb (i : Fin 6) : |q i+r i| ≤ (K+R)*boxWeight H u i := by
    calc
      _ ≤ |q i|+|r i| := abs_add _ _
      _ ≤ K*boxWeight H u i+R*boxWeight H u i := add_le_add (hq i) (hrw i i)
      _ = _ := by ring
  have hm (i j k : Fin 6) (h : boxWeight H u i ≤ boxWeight H u k) :
      |q i*r j| ≤ K*R*boxWeight H u k := by
    calc
      _ = |q i| * |r j| := abs_mul _ _
      _ ≤ (K*boxWeight H u k)*R :=
        mul_le_mul ((hq i).trans (mul_le_mul_of_nonneg_left h hK)) (hr j)
          (abs_nonneg _) (mul_nonneg hK (hw0 k))
      _ = _ := by ring
  have hp (i : Fin 6) : 0 ≤ K*R*boxWeight H u i :=
    mul_nonneg (mul_nonneg hK hR) (hw0 i)
  have finish (x y : Fin 6 → ℝ)
      (hbxy : ∀ i, |x i+y i| ≤ (K+R)*boxWeight H u i)
      (h013 : |x 0*y 3| ≤ K*R*boxWeight H u 1)
      (h024 : |x 0*y 4| ≤ K*R*boxWeight H u 2)
      (h125 : |x 1*y 5| ≤ K*R*boxWeight H u 2)
      (h345 : |x 3*y 5| ≤ K*R*boxWeight H u 4) :
      BoxBound (originalUpperAffineComp x y) (K+R+2*K*R) H u := by
    intro i
    fin_cases i
    · change |x 0+y 0| ≤ (K+R+2*K*R)*boxWeight H u 0
      nlinarith only [hbxy 0, hp 0]
    · change |x 1+y 1+x 0*y 3| ≤ (K+R+2*K*R)*boxWeight H u 1
      have hh := (abs_add _ _).trans (add_le_add (hbxy 1) h013)
      nlinarith only [hh, hp 1]
    · change |x 2+y 2+x 0*y 4+x 1*y 5| ≤ (K+R+2*K*R)*boxWeight H u 2
      have hh := (abs_add _ _).trans
        (add_le_add ((abs_add _ _).trans (add_le_add (hbxy 2) h024)) h125)
      nlinarith only [hh]
    · change |x 3+y 3| ≤ (K+R+2*K*R)*boxWeight H u 3
      nlinarith only [hbxy 3, hp 3]
    · change |x 4+y 4+x 3*y 5| ≤ (K+R+2*K*R)*boxWeight H u 4
      have hh := (abs_add _ _).trans (add_le_add (hbxy 4) h345)
      nlinarith only [hh, hp 4]
    · change |x 5+y 5| ≤ (K+R+2*K*R)*boxWeight H u 5
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

theorem boxBound_two_bounded (q l r : Fin 6 → ℝ) (K R H u : ℝ)
    (hH : 1 ≤ H) (hu : 0 ≤ u) (hK : 1 ≤ K) (hR : 1 ≤ R)
    (hq : BoxBound q K H u) (hl : ∀ i, |l i| ≤ R) (hr : ∀ i, |r i| ≤ R) :
    BoxBound (originalUpperAffineComp (originalUpperAffineComp l q) r)
      (16*K*R^2) H u := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
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
  have hleft := (boxBound_mul_bounded q l K R H u hH hu hK0 hR0 hq hl).2
  have hleft4 := boxBound_mono hH hu (hfour K hK) hleft
  have hright := (boxBound_mul_bounded (originalUpperAffineComp l q) r (4*K*R) R
    H u hH hu (zero_le_one.trans hfour1) hR0 hleft4 hr).1
  have hfinal := boxBound_mono hH hu (hfour (4*K*R) hfour1) hright
  convert hfinal using 1
  ring

/-- Undo both actual moving-gauge endpoints in their literal order. -/
def multiplyback (q : Fin 6 → ℝ) (tau0 tau eta0 eta : ℝ) : Fin 6 → ℝ :=
  ![q 0,q 1+tau0-tau-q 0*eta,q 2+tau0*q 5,
    q 3+eta0-eta,q 4+eta0*q 5,q 5]

theorem multiplyback_eq_comp (q : Fin 6 → ℝ) (tau0 tau eta0 eta : ℝ) :
    multiplyback q tau0 tau eta0 eta =
      originalUpperAffineComp
        (originalUpperAffineComp (originalUpperAffineInv (gaugeFrame tau0 eta0)) q)
        (gaugeFrame tau eta) := by
  ext i
  fin_cases i <;>
    simp [multiplyback,gaugeFrame,originalUpperAffineComp,originalUpperAffineInv] <;> ring

theorem gauged_relative_multiplyback (g0 g : Fin 6 → ℝ) (tau0 tau eta0 eta : ℝ) :
    multiplyback
      (originalUpperRelativeFrame (gaugePoint g0 tau0 eta0) (gaugePoint g tau eta))
      tau0 tau eta0 eta = originalUpperRelativeFrame g0 g := by
  ext i
  fin_cases i <;>
    simp [multiplyback,gaugePoint,gaugeFrame,originalUpperRelativeFrame,
      originalUpperAffineComp,originalUpperAffineInv] <;> ring

theorem multiplyback_box_bound (q : Fin 6 → ℝ) (K R H u tau0 tau eta0 eta : ℝ)
    (hH : 1 ≤ H) (hu : 0 ≤ u) (hK : 1 ≤ K) (hR : 1 ≤ R)
    (hq : BoxBound q K H u)
    (ht0 : |tau0| ≤ R) (ht : |tau| ≤ R) (he0 : |eta0| ≤ R) (he : |eta| ≤ R) :
    BoxBound (multiplyback q tau0 tau eta0 eta) (16*K*R^2) H u := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hl : ∀ i, |originalUpperAffineInv (gaugeFrame tau0 eta0) i| ≤ R := by
    intro i
    fin_cases i <;> simp [gaugeFrame_inverse] <;> assumption
  have hr : ∀ i, |gaugeFrame tau eta i| ≤ R := by
    intro i
    fin_cases i <;> simp [gaugeFrame] <;> assumption
  rw [multiplyback_eq_comp]
  exact boxBound_two_bounded q _ _ K R H u hH hu hK hR hq hl hr

end PaperI.OriginalFBox
