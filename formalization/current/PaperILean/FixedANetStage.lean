import PaperILean.FixedASliceRounding
import PaperILean.FixedDNetStage
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! I1593[155,246), I1982[28,50), I1983[62,85): the entire original
fixed-a sampling-net stage for cases 15 and 16. The finite catalog is fixed
before every source point, endpoint gauge and bounded comparison pair.
The preceding ODE integration and the table polytope conditions are not asserted. -/

noncomputable section
open scoped BigOperators
namespace PaperI.FixedANetStage
open FixedASliceRounding FixedABoxComparisons

def catalog (H U W K eps : ℝ) : Finset (Fin 5 → ℤ) :=
  Fintype.piFinset fun i => integerIntervalAround 0 ((6*K)*sliceWeight H U W i/eps)

def fixedANet (H U W K eps t : ℝ) : Finset (Fin 6 → ℝ) := by
  classical
  exact (catalog H U W K eps).image (latticeCenter eps t)

theorem sliceWeight_ge_one (H U W : ℝ) (hH : 1 ≤ H) (hU : 1 ≤ U)
    (hW : 1 ≤ W) (i : Fin 5) : 1 ≤ sliceWeight H U W i := by
  have hHU := one_le_mul_of_one_le_of_one_le hH hU
  have hUW := one_le_mul_of_one_le_of_one_le hU hW
  have hE : 1 ≤ H+U*W := by linarith
  have hC := one_le_mul_of_one_le_of_one_le hH hE
  fin_cases i <;> simp only [sliceWeight, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val] <;> assumption

theorem triIndex_mem_catalog (H U W K eps t : ℝ) (x : Fin 6 → ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hx : BoxBound x K H U W)
    (ht : x 0 = t) : triIndex eps t x ∈ catalog H U W K eps := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply mem_integerIntervalAround_of_abs_le
  simp only [sub_zero]
  apply (le_div_iff₀ heps).mpr
  have hh := rounded_center_bound H U W K eps t x hH hU hW hK heps heps1 hx ht i
  rw [abs_mul, abs_of_pos heps] at hh
  simpa only [mul_comm] using hh

private theorem interval_card_bound (w K eps : ℝ)
    (hw : 1 ≤ w) (hK : 1 ≤ K) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ((integerIntervalAround 0 ((6*K)*w/eps)).card : ℝ) ≤ (14*K/eps)*w := by
  have hw0 : 0 ≤ w := zero_le_one.trans hw
  have hr : 0 ≤ (6*K)*w/eps := div_nonneg (mul_nonneg (by linarith) hw0) heps.le
  have hh := integerIntervalAround_card_le 0 ((6*K)*w/eps) hr
  have hKw : w ≤ K*w := le_mul_of_one_le_left hw0 hK
  have hew : eps ≤ w := heps1.trans hw
  apply hh.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ heps).mpr
  calc
    (2*((6*K)*w/eps)+2)*eps = 2*((6*K)*w)+2*eps := by field_simp
    _ ≤ 14*K*w := by nlinarith only [hKw,hew]

theorem catalog_card_le (H U W K eps : ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ((catalog H U W K eps).card : ℝ) ≤
      (14*K/eps)^5*(H^2*U^2*W*(H+U*W)^2) := by
  change (((Fintype.piFinset fun i : Fin 5 =>
    integerIntervalAround 0 ((6*K)*sliceWeight H U W i/eps)).card : ℕ) : ℝ) ≤ _
  rw [Fintype.card_piFinset, Nat.cast_prod]
  calc
    (∏ i : Fin 5, ((integerIntervalAround 0 ((6*K)*sliceWeight H U W i/eps)).card : ℝ)) ≤
        ∏ i : Fin 5, (14*K/eps)*sliceWeight H U W i :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => interval_card_bound (sliceWeight H U W i) K eps
          (sliceWeight_ge_one H U W hH hU hW i) hK heps heps1)
    _ = _ := by
      simp [Fin.prod_univ_succ, sliceWeight]
      ring

theorem fixedANet_card_le (H U W K eps t : ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ((fixedANet H U W K eps t).card : ℝ) ≤
      (14*K/eps)^5*(H^2*U^2*W*(H+U*W)^2) := by
  classical
  exact (Nat.cast_le.mpr (Finset.card_image_le)).trans
    (catalog_card_le H U W K eps hH hU hW hK heps heps1)

theorem fixed_a_box_cover (H U W K eps t : ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ((fixedANet H U W K eps t).card : ℝ) ≤
        (14*K/eps)^5*(H^2*U^2*W*(H+U*W)^2) ∧
      ∀ x : Fin 6 → ℝ, x 0 = t → BoxBound x K H U W →
        ∃ c ∈ fixedANet H U W K eps t, c 0 = t ∧
          InRightACube eps (originalUpperRelativeFrame c x) := by
  classical
  refine ⟨fixedANet_card_le H U W K eps t hH hU hW hK heps heps1, ?_⟩
  intro x ht hx
  refine ⟨latticeCenter eps t (triIndex eps t x), ?_, ?_,
    rounded_relative_mem eps t x heps ht⟩
  · exact Finset.mem_image.mpr ⟨triIndex eps t x,
      triIndex_mem_catalog H U W K eps t x hH hU hW hK heps heps1 hx ht, rfl⟩
  · exact latticeCenter_fixed_a eps t (triIndex eps t x)

/-- Full restored-point coverage, including both bounded endpoint gauges and
both arbitrary bounded comparison factors, after the net has been fixed. -/
def CoversRestoredBox (N : Finset (Fin 6 → ℝ)) (P C D H u w t : ℝ) : Prop :=
  ∀ (q l r : Fin 6 → ℝ) (beta0 tau0 beta1 tau1 : ℝ),
    RawBoxBound q (P^C) H u w →
    |beta0| ≤ P^C → |tau0| ≤ P^C → |beta1| ≤ P^C → |tau1| ≤ P^C →
    (∀ i, |l i| ≤ P^C) → (∀ i, |r i| ≤ P^C) →
    restoredPoint q beta0 tau0 beta1 tau1 l r 0 = t →
    ∃ c ∈ N, c 0 = t ∧ InRightACube (P^(-D))
      (originalUpperRelativeFrame c (restoredPoint q beta0 tau0 beta1 tau1 l r))

theorem actual_fixed_a_product_net (P C D H u w t : ℝ)
    (hP : 2 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hH : 1 ≤ H) (hu : 0 ≤ u) (hw : 0 ≤ w) :
    let U := max 1 u
    let W := max 1 w
    let N := fixedANet H U W (P^(5*C+8)) (P^(-D)) t
    (N.card : ℝ) ≤ P^(25*C+5*D+60)*(H^2*U^2*W*(H+U*W)^2) ∧
      CoversRestoredBox N P C D H u w t := by
  dsimp only
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hK : 1 ≤ P^(5*C+8) := Real.one_le_rpow hP1 (by positivity)
  have heps : 0 < P^(-D) := Real.rpow_pos_of_pos hPpos _
  have heps1 : P^(-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hP1 (by linarith)
  have hc := fixed_a_box_cover H (max 1 u) (max 1 w) (P^(5*C+8)) (P^(-D)) t
    hH (le_max_left _ _) (le_max_left _ _) hK heps heps1
  refine ⟨hc.1.trans ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_right
    · convert FixedDNetStage.polynomial_card_factor P (5*C+8) D hP using 1 <;> ring
    · positivity
  · intro q l r beta0 tau0 beta1 tau1 hq hb0 ht0 hb1 ht1 hl hr ht
    exact hc.2 _ ht (restored_point_box_power q l r P C H u w beta0 tau0 beta1 tau1
      hP hC hH hu hw hq hb0 ht0 hb1 ht1 hl hr)

private theorem case15_product (H U W L : ℝ) (hH : 1 ≤ H)
    (hU : 1 ≤ U) (hW : 1 ≤ W) (hL : 1 ≤ L) (hb : U*W ≤ L*H) :
    H^2*U^2*W*(H+U*W)^2 ≤ 4*L^2*H^4*U^2*W := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hLH : H ≤ L*H := le_mul_of_one_le_left hH0 hL
  have hs : H+U*W ≤ 2*L*H := by linarith
  have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ H+U*W) hs 2
  calc
    _ ≤ H^2*U^2*W*(2*L*H)^2 := mul_le_mul_of_nonneg_left hs2 (by positivity)
    _ = _ := by ring

/-- The raw rates may be below one; positivity and the required max bounds
are consequences of the large-product hypotheses. -/
theorem case16_positive_max_bounds (H u w L : ℝ) (hH : 1 ≤ H)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hL : 1 ≤ L)
    (huH : u ≤ L*H) (hwH : w ≤ L*H) (hp : H ≤ L*u*w) :
    0 < u ∧ 0 < w ∧ max 1 u ≤ L^2*u ∧ max 1 w ≤ L^2*w := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hup : 0 < u := by
    by_contra hn
    have hz : u = 0 := le_antisymm (le_of_not_gt hn) hu
    rw [hz] at hp
    nlinarith only [hp,hHpos]
  have hwp : 0 < w := by
    by_contra hn
    have hz : w = 0 := le_antisymm (le_of_not_gt hn) hw
    rw [hz] at hp
    nlinarith only [hp,hHpos]
  have h1u : 1 ≤ L^2*u := by
    have hm := mul_le_mul_of_nonneg_left hwH (mul_nonneg hL0 hu)
    have hh : H*1 ≤ H*(L^2*u) := by nlinarith only [hp,hm]
    exact (mul_le_mul_left hHpos).mp hh
  have h1w : 1 ≤ L^2*w := by
    have hm := mul_le_mul_of_nonneg_right huH (mul_nonneg hL0 hw)
    have hh : H*1 ≤ H*(L^2*w) := by nlinarith only [hp,hm]
    exact (mul_le_mul_left hHpos).mp hh
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  exact ⟨hup,hwp,max_le h1u (le_mul_of_one_le_left hu hL2),
    max_le h1w (le_mul_of_one_le_left hw hL2)⟩

private theorem case16_product (H u w L : ℝ) (hH : 1 ≤ H)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hL : 1 ≤ L)
    (huH : u ≤ L*H) (hwH : w ≤ L*H) (hp : H ≤ L*u*w) :
    H^2*(max 1 u)^2*(max 1 w)*(H+max 1 u*max 1 w)^2 ≤
      4*L^14*H^2*u^4*w^3 := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hU0 : 0 ≤ max 1 u := zero_le_one.trans (le_max_left _ _)
  have hW0 : 0 ≤ max 1 w := zero_le_one.trans (le_max_left _ _)
  have hm := case16_positive_max_bounds H u w L hH hu hw hL huH hwH hp
  have hU := hm.2.2.1
  have hW := hm.2.2.2
  have hL4 : L ≤ L^4 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hL : 1 ≤ L^3) hL0
    nlinarith only [hh]
  have hUW : max 1 u*max 1 w ≤ L^4*u*w := by
    calc
      _ ≤ (L^2*u)*(L^2*w) := mul_le_mul hU hW hW0 (by positivity)
      _ = _ := by ring
  have hHuw : H ≤ L^4*u*w := hp.trans (by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL4 hu) hw)
  have hs : H+max 1 u*max 1 w ≤ 2*L^4*u*w := by linarith
  have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ H+max 1 u*max 1 w) hs 2
  have hU2 := pow_le_pow_left₀ hU0 hU 2
  calc
    _ ≤ H^2*(L^2*u)^2*(L^2*w)*(2*L^4*u*w)^2 := by
      apply mul_le_mul
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hU2 (sq_nonneg H)) hW hW0 (by positivity)
      · exact hs2
      · exact sq_nonneg _
      · positivity
    _ = _ := by ring

private theorem polynomial_regime_factor (P A R : ℝ) (n : ℕ) (hP : 2 ≤ P) :
    P^A*(4*(P^R)^n) ≤ P^(A+(n:ℝ)*R+2) := by
  have hPpos : 0 < P := by linarith
  have hP0 : 0 ≤ P := hPpos.le
  have h4 : (4:ℝ) ≤ P^2 := by nlinarith
  have heq : P^(A+(n:ℝ)*R+2) = P^A*((P^R)^n*P^2) := by
    rw [Real.rpow_add hPpos, Real.rpow_add hPpos,
      show (n:ℝ)*R=R*n by ring, Real.rpow_mul hP0]
    have h2 : P^(2:ℝ) = P^(2:ℕ) := Real.rpow_natCast P 2
    rw [Real.rpow_natCast (P^R) n, h2]
    ring
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hP0 A)
  nlinarith only [mul_le_mul_of_nonneg_left h4 (show 0 ≤ (P^R)^n by positivity)]

/-- The product form retains H=1 and both zero raw rates in case15. -/
theorem actual_fixed_a_case15_product_net (P C D R H u w t : ℝ)
    (hP : 2 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hH : 1 ≤ H) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hprod : max 1 u*max 1 w ≤ P^R*H) :
    let N := fixedANet H (max 1 u) (max 1 w) (P^(5*C+8)) (P^(-D)) t
    (N.card : ℝ) ≤ P^(25*C+5*D+2*R+62)*(H^4*(max 1 u)^2*max 1 w) ∧
      CoversRestoredBox N P C D H u w t := by
  dsimp only
  have hL : 1 ≤ P^R := Real.one_le_rpow (by linarith) hR
  have hc := actual_fixed_a_product_net P C D H u w t hP hC hD hH hu hw
  refine ⟨hc.1.trans ?_,hc.2⟩
  calc
    _ ≤ P^(25*C+5*D+60)*(4*(P^R)^2*H^4*(max 1 u)^2*max 1 w) :=
      mul_le_mul_of_nonneg_left
        (case15_product H (max 1 u) (max 1 w) (P^R) hH
          (le_max_left _ _) (le_max_left _ _) hL hprod) (by positivity)
    _ = (P^(25*C+5*D+60)*(4*(P^R)^2))*(H^4*(max 1 u)^2*max 1 w) := by ring
    _ ≤ P^(25*C+5*D+2*R+62)*(H^4*(max 1 u)^2*max 1 w) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      convert polynomial_regime_factor P (25*C+5*D+60) R 2 hP using 1 <;> ring

/-- The product form retains H=1; raw-rate positivity is not an extra premise. -/
theorem actual_fixed_a_case16_product_net (P C D R H u w t : ℝ)
    (hP : 2 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hH : 1 ≤ H) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (huH : u ≤ P^R*H) (hwH : w ≤ P^R*H) (hprod : H ≤ P^R*u*w) :
    let N := fixedANet H (max 1 u) (max 1 w) (P^(5*C+8)) (P^(-D)) t
    (N.card : ℝ) ≤ P^(25*C+5*D+14*R+62)*(H^2*u^4*w^3) ∧
      CoversRestoredBox N P C D H u w t := by
  dsimp only
  have hL : 1 ≤ P^R := Real.one_le_rpow (by linarith) hR
  have hc := actual_fixed_a_product_net P C D H u w t hP hC hD hH hu hw
  refine ⟨hc.1.trans ?_,hc.2⟩
  calc
    _ ≤ P^(25*C+5*D+60)*(4*(P^R)^14*H^2*u^4*w^3) :=
      mul_le_mul_of_nonneg_left
        (case16_product H u w (P^R) hH hu hw hL huH hwH hprod) (by positivity)
    _ = (P^(25*C+5*D+60)*(4*(P^R)^14))*(H^2*u^4*w^3) := by ring
    _ ≤ P^(25*C+5*D+14*R+62)*(H^2*u^4*w^3) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      convert polynomial_regime_factor P (25*C+5*D+60) R 14 hP using 1 <;> ring

private theorem case15_log_identity (H U W : ℝ) (hH : 1 < H)
    (hU : 0 < U) (hW : 0 < W) :
    H^(4+2*Real.logb H U+Real.logb H W) = H^4*U^2*W := by
  have hHpos : 0 < H := by linarith
  have hHne : H ≠ 1 := ne_of_gt hH
  rw [Real.rpow_add hHpos, Real.rpow_add hHpos,
    show (2:ℝ)*Real.logb H U=Real.logb H U*2 by ring, Real.rpow_mul hHpos.le]
  rw [Real.rpow_logb hHpos hHne hU, Real.rpow_logb hHpos hHne hW]
  exact congrArg (fun z : ℝ => z*W)
    (congrArg₂ (fun a b : ℝ => a*b) (Real.rpow_natCast H 4) (Real.rpow_natCast U 2))

private theorem case16_log_identity (H u w : ℝ) (hH : 1 < H)
    (hu : 0 < u) (hw : 0 < w) :
    H^(2+4*Real.logb H u+3*Real.logb H w) = H^2*u^4*w^3 := by
  have hHpos : 0 < H := by linarith
  have hHne : H ≠ 1 := ne_of_gt hH
  rw [Real.rpow_add hHpos, Real.rpow_add hHpos,
    show (4:ℝ)*Real.logb H u=Real.logb H u*4 by ring,
    show (3:ℝ)*Real.logb H w=Real.logb H w*3 by ring,
    Real.rpow_mul hHpos.le, Real.rpow_mul hHpos.le]
  rw [Real.rpow_logb hHpos hHne hu, Real.rpow_logb hHpos hHne hw]
  exact congrArg₂ (fun a b : ℝ => a*b)
    (congrArg₂ (fun a b : ℝ => a*b) (Real.rpow_natCast H 2) (Real.rpow_natCast u 4))
    (Real.rpow_natCast w 3)

/-- The case15 table exponent, with one deterministic actual original net.
The raw zero-rate cases are allowed; only the table logarithms require H>1. -/
theorem actual_fixed_a_case15_net (P C D R H u w t : ℝ)
    (hP : 2 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hH : 1 < H) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hprod : max 1 u*max 1 w ≤ P^R*H) :
    let N := fixedANet H (max 1 u) (max 1 w) (P^(5*C+8)) (P^(-D)) t
    (N.card : ℝ) ≤ P^(25*C+5*D+2*R+62)*
        H^(4+2*Real.logb H (max 1 u)+Real.logb H (max 1 w)) ∧
      CoversRestoredBox N P C D H u w t := by
  dsimp only
  have hU0 : 0 < max 1 u := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hW0 : 0 < max 1 w := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [case15_log_identity H (max 1 u) (max 1 w) hH hU0 hW0]
  exact actual_fixed_a_case15_product_net P C D R H u w t hP hC hD hR hH.le hu hw hprod

/-- The case16 table exponent uses the raw positive rates, including subunit
rates with negative logarithms. Positivity is proved from the regime hypotheses. -/
theorem actual_fixed_a_case16_net (P C D R H u w t : ℝ)
    (hP : 2 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hH : 1 < H) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (huH : u ≤ P^R*H) (hwH : w ≤ P^R*H) (hprod : H ≤ P^R*u*w) :
    let N := fixedANet H (max 1 u) (max 1 w) (P^(5*C+8)) (P^(-D)) t
    (N.card : ℝ) ≤ P^(25*C+5*D+14*R+62)*
        H^(2+4*Real.logb H u+3*Real.logb H w) ∧
      CoversRestoredBox N P C D H u w t := by
  dsimp only
  have hL : 1 ≤ P^R := Real.one_le_rpow (by linarith) hR
  have hm := case16_positive_max_bounds H u w (P^R) hH.le hu hw hL huH hwH hprod
  rw [case16_log_identity H u w hH hm.1 hm.2.1]
  exact actual_fixed_a_case16_product_net P C D R H u w t hP hC hD hR hH.le hu hw huH hwH hprod

end PaperI.FixedANetStage
