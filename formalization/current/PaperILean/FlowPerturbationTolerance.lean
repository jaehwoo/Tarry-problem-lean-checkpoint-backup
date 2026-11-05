import PaperILean.OriginalUpperFlowPerturbation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! I1480[363,533): uniform inverse-power perturbation tolerance for the
actual original upper-affine flow. The exponent is fixed before P, paths,
anchors and their interval. No positivity restriction is imposed on the
requested target exponent or on the two polynomial-window exponents. -/

noncomputable section
open Set

namespace PaperI.FlowPerturbationTolerance

/-- The tolerance exponent for body and interval polynomial windows. -/
noncomputable def flowToleranceExponent (Cm CL target : ℝ) : ℝ :=
  target + 5 + 2 * max Cm 0 + 3 * max CL 0

/-- The literal degree-three perturbation polynomial is bounded uniformly
on the two stated power windows. -/
theorem polynomial_window_bound (P M L Cm CL : ℝ) (hP : 2 ≤ P)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hMw : M ≤ P ^ Cm) (hLw : L ≤ P ^ CL) :
    L + 4 * M * L ^ 2 + 3 * M ^ 2 * L ^ 3 ≤
      8 * P ^ (2 * max Cm 0 + 3 * max CL 0) := by
  have hpos : 0 < P := by linarith
  have hone : 1 ≤ P := by linarith
  have hr : 0 ≤ max Cm 0 := le_max_right _ _
  have hs : 0 ≤ max CL 0 := le_max_right _ _
  have hMr : M ≤ P ^ (max Cm 0) := hMw.trans
    (Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _))
  have hLs : L ≤ P ^ (max CL 0) := hLw.trans
    (Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _))
  have hp2 (x : ℝ) : (P ^ x) ^ 2 = P ^ (2 * x) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  have hp3 (x : ℝ) : (P ^ x) ^ 3 = P ^ (3 * x) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  have hLQ : L ≤ P ^ (2 * max Cm 0 + 3 * max CL 0) := hLs.trans
    (Real.rpow_le_rpow_of_exponent_le hone (by linarith))
  have hMLQ : M * L ^ 2 ≤ P ^ (2 * max Cm 0 + 3 * max CL 0) := by
    calc
      _ ≤ P ^ (max Cm 0) * (P ^ (max CL 0)) ^ 2 :=
        mul_le_mul hMr (pow_le_pow_left₀ hL hLs 2) (sq_nonneg L)
          (Real.rpow_nonneg hpos.le _)
      _ = P ^ (max Cm 0 + 2 * max CL 0) := by
        rw [hp2, ← Real.rpow_add hpos]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hone (by linarith)
  have hMMLQ : M ^ 2 * L ^ 3 ≤ P ^ (2 * max Cm 0 + 3 * max CL 0) := by
    calc
      _ ≤ (P ^ (max Cm 0)) ^ 2 * (P ^ (max CL 0)) ^ 3 :=
        mul_le_mul (pow_le_pow_left₀ hM hMr 2) (pow_le_pow_left₀ hL hLs 3)
          (pow_nonneg hL 3) (sq_nonneg _)
      _ = _ := by rw [hp2, hp3, ← Real.rpow_add hpos]
  nlinarith

/-- The chosen exponent absorbs the Euclidean factor sqrt(6), the cubic
flow polynomial and arbitrary real source exponents, including negative ones. -/
theorem tolerance_error_bound (P M L Cm CL target : ℝ) (hP : 2 ≤ P)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hMw : M ≤ P ^ Cm) (hLw : L ≤ P ^ CL) :
    Real.sqrt 6 * (P ^ (-flowToleranceExponent Cm CL target) *
      (L + 4 * M * L ^ 2 + 3 * M ^ 2 * L ^ 3)) ≤ P ^ (-target) := by
  have hpos : 0 < P := by linarith
  have heps : 0 ≤ P ^ (-flowToleranceExponent Cm CL target) :=
    Real.rpow_nonneg hpos.le _
  have hQ : 0 ≤ P ^ (2 * max Cm 0 + 3 * max CL 0) :=
    Real.rpow_nonneg hpos.le _
  have hF : 0 ≤ L + 4 * M * L ^ 2 + 3 * M ^ 2 * L ^ 3 := by positivity
  have hsqrt : Real.sqrt 6 ≤ 4 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h32 : (32 : ℝ) ≤ P ^ (5 : ℝ) := by
    change (32 : ℝ) ≤ P ^ ((5 : ℕ) : ℝ)
    rw [Real.rpow_natCast]
    calc
      (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      _ ≤ P ^ (5 : ℕ) := pow_le_pow_left₀ (by norm_num) hP 5
  have hp := polynomial_window_bound P M L Cm CL hP hM hL hMw hLw
  calc
    _ = Real.sqrt 6 * P ^ (-flowToleranceExponent Cm CL target) *
        (L + 4 * M * L ^ 2 + 3 * M ^ 2 * L ^ 3) := by ring
    _ ≤ 4 * P ^ (-flowToleranceExponent Cm CL target) *
        (8 * P ^ (2 * max Cm 0 + 3 * max CL 0)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hsqrt heps) hp hF (by positivity)
    _ = 32 * P ^ (-flowToleranceExponent Cm CL target) *
        P ^ (2 * max Cm 0 + 3 * max CL 0) := by ring
    _ ≤ P ^ (5 : ℝ) * P ^ (-flowToleranceExponent Cm CL target) *
        P ^ (2 * max Cm 0 + 3 * max CL 0) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h32 heps) hQ
    _ = P ^ (-target) := by
      rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]
      congr 1
      unfold flowToleranceExponent
      ring

/-- Uniform source-stage consequence for the actual relative frames and
their literal homogeneous affine matrices, in either direction of travel.
The body-rate and interval windows are retained, without any bound on the
initial frames and without assuming the desired output error. -/
theorem original_upper_flow_power_tolerance_stage
    (Cm CL target P : ℝ) (hP : 2 ≤ P)
    (g h b c : ℝ → Fin 6 → ℝ) (a z M : ℝ)
    (hb : ContinuousOn b (uIcc a z)) (hc : ContinuousOn c (uIcc a z))
    (hg : ∀ t ∈ uIcc a z,
      HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t)
    (hh : ∀ t ∈ uIcc a z,
      HasDerivAt h (originalUpperBodyVelocity (h t) (c t)) t)
    (hbM : ∀ t ∈ uIcc a z, ∀ i : Fin 6, |b t i| ≤ M)
    (hcM : ∀ t ∈ uIcc a z, ∀ i : Fin 6, |c t i| ≤ M)
    (hMw : M ≤ P ^ Cm) (hLw : |z - a| ≤ P ^ CL)
    (herr : ∀ t ∈ uIcc a z, ∀ i : Fin 6,
      |b t i - c t i| ≤ P ^ (-flowToleranceExponent Cm CL target)) :
    coordinateL2Norm (originalUpperRelativeFrame (g a) (g z) -
      originalUpperRelativeFrame (h a) (h z)) ≤ P ^ (-target) ∧
    coordinateL2Norm (fun ij : Fin 4 × Fin 4 =>
      (originalAffineHomogeneousMatrix (originalUpperRelativeFrame (g a) (g z)) -
        originalAffineHomogeneousMatrix (originalUpperRelativeFrame (h a) (h z)))
        ij.1 ij.2) ≤ P ^ (-target) := by
  have hM : 0 ≤ M := (abs_nonneg (b a 0)).trans (hbM a left_mem_uIcc 0)
  have hscalar := tolerance_error_bound P M |z - a| Cm CL target hP hM
    (abs_nonneg _) hMw hLw
  have hflow := OriginalUpperFlowPerturbation.original_upper_flow_perturbation_stage
    g h b c a z M (P ^ (-flowToleranceExponent Cm CL target))
    hb hc hg hh hbM hcM herr
  exact ⟨hflow.1.trans hscalar, hflow.2.trans hscalar⟩

end PaperI.FlowPerturbationTolerance
