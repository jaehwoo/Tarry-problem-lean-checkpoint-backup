import PaperILean.JointPolynomialSmoothness
import PaperILean.TensorFrameBounds
import PaperILean.CompleteJetNormEquivalence
import Mathlib.Analysis.Normed.Group.Bounded

/-! I255: raw derivatives on a bounded set. Constants precede the coefficient
vector, center, derivative order and radius. Full ordered HS norms and actual
iterated derivatives are retained. Compactness makes the elementary finite-
dimensional polynomial bound explicit; no closedness/nonemptiness of X is needed.
-/
noncomputable section
open scoped BigOperators
namespace PaperI

theorem continuous_tensorHSNorm (r : ℕ) :
    Continuous (fun T : TensorSpace r => tensorHSNorm T) := by
  unfold tensorHSNorm coordinateL2Norm tensorCoordinates
  apply Real.continuous_sqrt.comp
  exact continuous_finset_sum _ (fun a _ => (continuous_id.eval continuous_const).pow 2)

theorem continuous_rawJetHSNorm_joint {k : ℕ} (r : ℕ) :
    Continuous (fun p : CoefficientSpace k × PhysicalSpace =>
      tensorHSNorm (iteratedFDeriv ℝ r (phase p.1) p.2)) :=
  (continuous_tensorHSNorm r).comp (contDiff_iteratedFDeriv_phase_joint r).continuous

theorem rawJetHSNorm_smul {k : ℕ} (a : ℝ) (F : CoefficientSpace k)
    (c : PhysicalSpace) (r : ℕ) :
    tensorHSNorm (iteratedFDeriv ℝ r (phase (a • F)) c) =
      |a| * tensorHSNorm (iteratedFDeriv ℝ r (phase F) c) := by
  rw [phase_smul_eq, iteratedFDeriv_const_smul_apply (contDiff_phase F _).contDiffAt,
    tensorHSNorm_smul]

def rawJetSum {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace) : ℝ :=
  ∑ r ∈ Finset.range (k + 1), tensorHSNorm (iteratedFDeriv ℝ r (phase F) c)

theorem rawJetSum_nonneg {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace) :
    0 ≤ rawJetSum F c :=
  Finset.sum_nonneg (fun _ _ => tensorHSNorm_nonneg _)

theorem continuous_rawJetSum_joint {k : ℕ} :
    Continuous (fun p : CoefficientSpace k × PhysicalSpace => rawJetSum p.1 p.2) :=
  continuous_finset_sum _ (fun r _ => continuous_rawJetHSNorm_joint r)

theorem rawJetSum_smul {k : ℕ} (a : ℝ) (F : CoefficientSpace k) (c : PhysicalSpace) :
    rawJetSum (a • F) c = |a| * rawJetSum F c := by
  simp only [rawJetSum, rawJetHSNorm_smul, Finset.mul_sum]

theorem rawJetSum_zero (k : ℕ) (c : PhysicalSpace) : rawJetSum (0 : CoefficientSpace k) c = 0 := by
  simpa using rawJetSum_smul 0 (0 : CoefficientSpace k) c

theorem rawJetHSNorm_le_sum {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (r : ℕ) (hr : r ≤ k) :
    tensorHSNorm (iteratedFDeriv ℝ r (phase F) c) ≤ rawJetSum F c := by
  unfold rawJetSum
  exact Finset.single_le_sum
    (fun n _ => tensorHSNorm_nonneg (iteratedFDeriv ℝ n (phase F) c))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))

theorem coefficient_pi_norm_le_euclidean {k : ℕ} (F : CoefficientSpace k) :
    ‖F‖ ≤ coefficientEuclideanNorm F := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro a
  exact (Real.norm_eq_abs _).le.trans (abs_le_sqrt_sum_sq F a)

theorem rawJetSum_uniform_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : CoefficientSpace k) (c : PhysicalSpace),
      c ∈ X → rawJetSum F c ≤ C * coefficientEuclideanNorm F := by
  obtain ⟨d, hd⟩ := hX.subset_closedBall (0 : PhysicalSpace)
  have hK := (isCompact_closedBall (0 : CoefficientSpace k) 1).prod
    (isCompact_closedBall (0 : PhysicalSpace) d)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (continuous_rawJetSum_joint (k := k)).continuousOn
  let C : ℝ := max 1 M
  have hC : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  refine ⟨C, hC, ?_⟩
  intro F c hc
  have hlinear : rawJetSum F c ≤ C * ‖F‖ := by
    by_cases hF : F = 0
    · simp [hF, rawJetSum_zero]
    have hn : ‖F‖ ≠ 0 := norm_ne_zero_iff.mpr hF
    have hn0 : 0 < ‖F‖ := norm_pos_iff.mpr hF
    have hunit : ‖F‖⁻¹ • F ∈ Metric.closedBall (0 : CoefficientSpace k) 1 := by
      simp [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg F)), inv_mul_cancel₀ hn]
    have hh := hM (‖F‖⁻¹ • F, c) ⟨hunit, hd hc⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (rawJetSum_nonneg _ _), rawJetSum_smul,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg F))] at hh
    have hm : ‖F‖⁻¹ * rawJetSum F c ≤ C := hh.trans (le_max_right _ _)
    calc
      rawJetSum F c = ‖F‖ * (‖F‖⁻¹ * rawJetSum F c) := by field_simp
      _ ≤ ‖F‖ * C := mul_le_mul_of_nonneg_left hm hn0.le
      _ = C * ‖F‖ := mul_comm _ _
  exact hlinear.trans (mul_le_mul_of_nonneg_left (coefficient_pi_norm_le_euclidean F) hC0)

theorem rawJetHSNorm_uniform_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : CoefficientSpace k) (c : PhysicalSpace),
      c ∈ X → ∀ r : ℕ, r ≤ k →
        tensorHSNorm (iteratedFDeriv ℝ r (phase F) c) ≤ C * coefficientEuclideanNorm F := by
  obtain ⟨C, hC, hb⟩ := rawJetSum_uniform_bound k X hX
  exact ⟨C, hC, fun F c hc r hr => (rawJetHSNorm_le_sum F c r hr).trans (hb F c hc)⟩

theorem source_rawJetHSNorm_uniform_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ (F : CoefficientSpace k),
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X →
      ∀ r : ℕ, 2 ≤ r → r ≤ k →
        tensorHSNorm (iteratedFDeriv ℝ r (phase F) c) ≤ C * R := by
  obtain ⟨C, hC, hb⟩ := rawJetHSNorm_uniform_bound k X hX
  refine ⟨2 * C, by linarith, ?_⟩
  intro R _ F hF c hc r _ hr
  calc
    _ ≤ C * coefficientEuclideanNorm F := hb F c hc r hr
    _ ≤ C * (2 * R) := mul_le_mul_of_nonneg_left hF (by linarith)
    _ = (2 * C) * R := by ring

end PaperI
