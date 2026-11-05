import PaperILean.FixedFBoxCover

/-! Complete fixed-f covering estimate at I1574[48,88).
The deterministic original-coordinate net covers the entire enlarged box slice.
The mesh parameter is explicit; no covering, admissibility, sampling, or
common-cover assignment premise is assumed. -/
noncomputable section
namespace PaperI.FixedFNetStage
open FixedFSliceRounding FixedFBoxCover

/-- Explicit uniform P-power budget for the five-dimensional net. -/
theorem polynomial_card_factor (P C D : ℝ) (hP : 2 ≤ P) :
    (10 * P^C / P^(-D))^5 ≤ P^(5*C+5*D+20) := by
  have hPpos : 0 < P := by linarith
  have hP0 : 0 ≤ P := hPpos.le
  have hfour : (10 : ℝ) ≤ P^4 := by
    have h2 : (4 : ℝ) ≤ P^2 := by nlinarith
    nlinarith [sq_nonneg (P^2-4)]
  have hf : 10 * P^C / P^(-D) ≤ P^(C+D+4) := by
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

/-- The source N_f estimate, with a concrete net and explicit P exponent.
Every net point has the prescribed original f-coordinate and each right
comparison lies in a half-open coordinate cube of side P^(-D). -/
theorem actual_fixed_f_net_stage (P C D H u F : ℝ)
    (hP : 2 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D) (hH : 1 ≤ H) (hu : 0 ≤ u) :
    let N := fixedFNet H u (P^C) (P^(-D)) F
    (N.card : ℝ) ≤ P^(5*C+5*D+20) * H^2 * (max H u)^3 * max 1 (u/H) ∧
    ∀ x : Fin 6 → ℝ, x 5 = F → SliceBoxBound x (P^C) H u →
      ∃ c ∈ N, c 5 = F ∧ InRightCube (P^(-D)) (originalUpperRelativeFrame c x) := by
  dsimp only
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hK : 1 ≤ P^C := Real.one_le_rpow hP1 hC
  have heps : 0 < P^(-D) := Real.rpow_pos_of_pos hPpos _
  have heps1 : P^(-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hP1 (by linarith)
  have hc := fixed_f_box_cover H u (P^C) (P^(-D)) F hH hK heps heps1
  refine ⟨hc.1.trans ?_, hc.2⟩
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (polynomial_card_factor P C D hP) (sq_nonneg H)
    · exact pow_nonneg (hu.trans (le_max_right H u)) 3
  · exact zero_le_one.trans (le_max_left 1 (u/H))

end PaperI.FixedFNetStage
