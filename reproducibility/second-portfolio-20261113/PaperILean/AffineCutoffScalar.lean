import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

open scoped ENNReal

namespace PaperI.AffineCutoffScalar

/-- Positive curvature and affine factors force finite parameter volume from a
finite physical curvature-area bound. No finite-volume premise is assumed. -/
theorem cutoff_scalar (V A AB : ℝ≥0∞) (κ v Ubound : ℝ)
    (hκ : 0 < κ) (hv : 0 < v) (hU : 0 ≤ Ubound)
    (hlow : ENNReal.ofReal (κ ^ (1 / 4 : ℝ)) * V ≤ A)
    (htrans : AB = ENNReal.ofReal (v ^ (1 / 2 : ℝ)) * A)
    (hup : AB ≤ ENNReal.ofReal Ubound) :
    V ≤ ENNReal.ofReal (Ubound * κ ^ (-1 / 4 : ℝ) * v ^ (-1 / 2 : ℝ)) ∧
    V ≠ ∞ ∧ V.toReal ≤ Ubound * κ ^ (-1 / 4 : ℝ) * v ^ (-1 / 2 : ℝ) := by
  let q : ℝ := κ ^ (1 / 4 : ℝ)
  let s : ℝ := v ^ (1 / 2 : ℝ)
  have hq : 0 < q := Real.rpow_pos_of_pos hκ _
  have hs : 0 < s := Real.rpow_pos_of_pos hv _
  have hp : 0 < s * q := mul_pos hs hq
  have hproduct : ENNReal.ofReal (s * q) * V ≤ ENNReal.ofReal Ubound := by
    rw [ENNReal.ofReal_mul hs.le, mul_assoc]
    exact (mul_le_mul_left' hlow (ENNReal.ofReal s)).trans (htrans ▸ hup)
  have hb : V ≤ ENNReal.ofReal ((s * q)⁻¹ * Ubound) := by
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hp.le), ENNReal.ofReal_inv_of_pos hp]
    exact (ENNReal.mul_le_iff_le_inv (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
      ENNReal.ofReal_ne_top).mp hproduct
  have hform : (s * q)⁻¹ * Ubound =
      Ubound * κ ^ (-1 / 4 : ℝ) * v ^ (-1 / 2 : ℝ) := by
    dsimp [s, q]
    rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring,
      show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hκ.le, Real.rpow_neg hv.le]
    simp only [mul_inv_rev]
    ring
  rw [hform] at hb
  refine ⟨hb, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb, ?_⟩
  have hnonneg : 0 ≤ Ubound * κ ^ (-1 / 4 : ℝ) * v ^ (-1 / 2 : ℝ) := by positivity
  simpa only [ENNReal.toReal_ofReal hnonneg] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

end PaperI.AffineCutoffScalar
