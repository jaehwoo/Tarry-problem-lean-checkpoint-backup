import PaperILean.FixedDSliceRounding
import PaperILean.IntegerPointBoxes

/-! I1523[35,66), interpreted by I1525[0,68): the whole original-coordinate
box has a finite fixed-d sampling cover. The catalog is chosen before the
point or phase, and its count is uniform in the prescribed d-coordinate. -/

noncomputable section
open scoped BigOperators
namespace PaperI.FixedDNetStage
open FixedDSliceRounding OriginalDGaugeBox

/-- The integer catalog is independent of the point, phase and fixed d-value. -/
def catalog (H U W K eps : ℝ) : Finset (Fin 5 → ℤ) :=
  Fintype.piFinset fun i => integerIntervalAround 0 ((3*K+3)*sliceWeight H U W i/eps)

def fixedDNet (H U W K eps t : ℝ) : Finset (Fin 6 → ℝ) := by
  classical
  exact (catalog H U W K eps).image (latticeCenter eps t)

theorem sliceWeight_ge_one (H U W : ℝ) (hH : 1 ≤ H) (hU : 1 ≤ U)
    (hW : 1 ≤ W) (i : Fin 5) : 1 ≤ sliceWeight H U W i := by
  have hHU := one_le_mul_of_one_le_of_one_le hH hU
  have hHW := one_le_mul_of_one_le_of_one_le hH hW
  have hHUW := one_le_mul_of_one_le_of_one_le hHU hW
  fin_cases i <;> simp only [sliceWeight, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val] <;> assumption

theorem triIndex_mem_catalog (H U W K eps t : ℝ) (x : Fin 6 → ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hx : BoxBound x K H U W)
    (ht : x 3 = t) : triIndex eps t x ∈ catalog H U W K eps := by
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
    ((integerIntervalAround 0 ((3*K+3)*w/eps)).card : ℝ) ≤ (14*K/eps)*w := by
  have hw0 : 0 ≤ w := zero_le_one.trans hw
  have hr : 0 ≤ (3*K+3)*w/eps := div_nonneg (mul_nonneg (by linarith) hw0) heps.le
  have hh := integerIntervalAround_card_le 0 ((3*K+3)*w/eps) hr
  have hKw : w ≤ K*w := le_mul_of_one_le_left hw0 hK
  have hew : eps ≤ w := heps1.trans hw
  apply hh.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ heps).mpr
  calc
    (2*((3*K+3)*w/eps)+2)*eps = 2*((3*K+3)*w)+2*eps := by field_simp
    _ ≤ 14*K*w := by nlinarith only [hKw,hew]

theorem catalog_card_le (H U W K eps : ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ((catalog H U W K eps).card : ℝ) ≤ (14*K/eps)^5*H^3*U^3*W^3 := by
  change (((Fintype.piFinset fun i : Fin 5 =>
    integerIntervalAround 0 ((3*K+3)*sliceWeight H U W i/eps)).card : ℕ) : ℝ) ≤ _
  rw [Fintype.card_piFinset, Nat.cast_prod]
  calc
    (∏ i : Fin 5, ((integerIntervalAround 0 ((3*K+3)*sliceWeight H U W i/eps)).card : ℝ)) ≤
        ∏ i : Fin 5, (14*K/eps)*sliceWeight H U W i :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => interval_card_bound (sliceWeight H U W i) K eps
          (sliceWeight_ge_one H U W hH hU hW i) hK heps heps1)
    _ = _ := by
      simp [Fin.prod_univ_succ, sliceWeight]
      ring

theorem fixedDNet_card_le (H U W K eps t : ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ((fixedDNet H U W K eps t).card : ℝ) ≤ (14*K/eps)^5*H^3*U^3*W^3 := by
  classical
  exact (Nat.cast_le.mpr (Finset.card_image_le)).trans
    (catalog_card_le H U W K eps hH hU hW hK heps heps1)

/-- Every point of the source box at fixed d has a center in the fixed finite
catalog. Its original right-relative residual lies in the mesh cube with D=0. -/
theorem fixed_d_box_cover (H U W K eps t : ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ((fixedDNet H U W K eps t).card : ℝ) ≤ (14*K/eps)^5*H^3*U^3*W^3 ∧
      ∀ x : Fin 6 → ℝ, x 3 = t → BoxBound x K H U W →
        ∃ c ∈ fixedDNet H U W K eps t, c 3 = t ∧
          InRightDCube eps (originalUpperRelativeFrame c x) := by
  classical
  refine ⟨fixedDNet_card_le H U W K eps t hH hU hW hK heps heps1, ?_⟩
  intro x ht hx
  refine ⟨latticeCenter eps t (triIndex eps t x), ?_, ?_,
    rounded_relative_mem eps t x heps ht⟩
  · exact Finset.mem_image.mpr ⟨triIndex eps t x,
      triIndex_mem_catalog H U W K eps t x hH hU hW hK heps heps1 hx ht, rfl⟩
  · exact latticeCenter_fixed_d eps t (triIndex eps t x)

theorem polynomial_card_factor (P C D : ℝ) (hP : 2 ≤ P) :
    (14 * P^C / P^(-D))^5 ≤ P^(5*C+5*D+20) := by
  have hPpos : 0 < P := by linarith
  have hP0 : 0 ≤ P := hPpos.le
  have hfour : (14 : ℝ) ≤ P^4 := by
    have h2 : (4 : ℝ) ≤ P^2 := by nlinarith
    nlinarith [sq_nonneg (P^2-4)]
  have hf : 14 * P^C / P^(-D) ≤ P^(C+D+4) := by
    rw [Real.rpow_neg hP0, div_inv_eq_mul]
    have heq : P^(C+D+4) = P^C * P^D * P^4 := by
      rw [Real.rpow_add hPpos, Real.rpow_add hPpos]
      exact congrArg (fun x : ℝ => P^C * P^D * x) (Real.rpow_natCast P 4)
    rw [heq]
    nlinarith only [mul_le_mul_of_nonneg_right hfour
      (mul_nonneg (Real.rpow_nonneg hP0 C) (Real.rpow_nonneg hP0 D))]
  have heq : (P^(C+D+4))^5 = P^(5*C+5*D+20) := by
    rw [← Real.rpow_natCast (P^(C+D+4)) 5, ← Real.rpow_mul hP0]
    congr 1
    ring
  rw [← heq]
  exact pow_le_pow_left₀ (by positivity) hf 5

/-- Complete fixed-d sampling estimate at I1523[35,66), with an explicit
P-power loss and a deterministic whole-box covering net. -/
theorem actual_fixed_d_net_stage (P C D H U W t : ℝ)
    (hP : 2 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) :
    let N := fixedDNet H U W (P^C) (P^(-D)) t
    (N.card : ℝ) ≤ P^(5*C+5*D+20)*H^3*U^3*W^3 ∧
      ∀ x : Fin 6 → ℝ, x 3 = t → BoxBound x (P^C) H U W →
        ∃ c ∈ N, c 3 = t ∧ InRightDCube (P^(-D)) (originalUpperRelativeFrame c x) := by
  dsimp only
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hK : 1 ≤ P^C := Real.one_le_rpow hP1 hC
  have heps : 0 < P^(-D) := Real.rpow_pos_of_pos hPpos _
  have heps1 : P^(-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hP1 (by linarith)
  have hc := fixed_d_box_cover H U W (P^C) (P^(-D)) t hH hU hW hK heps heps1
  refine ⟨hc.1.trans ?_,hc.2⟩
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (polynomial_card_factor P C D hP)
        (pow_nonneg (zero_le_one.trans hH) 3)
    · exact pow_nonneg (zero_le_one.trans hU) 3
  · exact pow_nonneg (zero_le_one.trans hW) 3

end PaperI.FixedDNetStage
