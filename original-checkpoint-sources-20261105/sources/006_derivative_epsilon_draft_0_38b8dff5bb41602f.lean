import PaperILean.GraphMonotonicityDefinability
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
open Set Filter Asymptotics
open scoped Topology
namespace PaperI
example {u v : ℝ} (hv : 0 ≤ v) : u^2 ≤ v^2 ↔ |u| ≤ v := by
  exact (sq_le_sq₀ (abs_nonneg u) hv).symm.trans (by rw [sq_abs])
example {f : ℝ → ℝ} {m x : ℝ} : HasDerivAt f m x ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ,
      (t-x)^2 < δ^2 → (f t-f x-m*(t-x))^2 ≤ ε^2*(t-x)^2 := by
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp (h hε)
    refine ⟨δ, hδ, fun t ht => ?_⟩
    have ht' : dist t x < δ := by
      rw [Real.dist_eq]
      exact (sq_lt_sq₀ (abs_nonneg (t-x)) hδ.le).mp (by simpa only [sq_abs] using ht)
    have hb := hbound ht'
    simp only [Real.norm_eq_abs, smul_eq_mul] at hb
    have hs := (sq_le_sq₀ (abs_nonneg (f t-f x-(t-x)*m))
      (mul_nonneg hε.le (abs_nonneg (t-x)))).mpr hb
    simpa only [sq_abs, mul_pow, mul_comm] using hs
  · intro h ε hε
    obtain ⟨δ,hδ,hbound⟩ := h ε hε
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨δ,hδ,fun t ht => ?_⟩
    have ht' : (t-x)^2 < δ^2 := by
      simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (t-x)) hδ.le).mpr
        (by simpa only [Real.dist_eq] using ht)
    have hb := hbound t ht'
    simp only [Real.norm_eq_abs, smul_eq_mul]
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hε.le (abs_nonneg _))).mp
    simpa only [sq_abs, mul_pow, mul_comm] using hb
end PaperI
