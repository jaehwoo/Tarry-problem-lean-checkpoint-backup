import PaperILean.RelativeFrameBootstrap
import Mathlib.Analysis.Normed.Module.Convex

/-! I270--276, I298: the local relative comparison for actual minimizing frames.
Constants are chosen before R, F, both centers and the initial representative.
The center path is controlled on the bounded convex hull of X; no convexity
hypothesis on the source's fixed bounded center set is added. -/
noncomputable section
open Set
open scoped Matrix Matrix.L2OpNorm ContDiff
namespace PaperI

theorem source_minimizingFrame_local_comparison (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) (CX C0 : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) :
    ∃ ccmp Kcmp : ℝ, 0 < ccmp ∧ 0 < Kcmp ∧
      ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R →
      ∀ c ∈ X, ∀ c' ∈ X, ∀ B₀ : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c (sourceRegularization CX C0 R) B₀.val ≤
        FrameEnergy F c (sourceRegularization CX C0 R) D.val) →
      physicalEuclideanNorm (B₀.val⁻¹ *ᵥ (c' - c)) ≤
        ccmp * Real.sqrt (sourceRegularization CX C0 R) →
      ∃ B' : PositiveFrame,
        (∀ D : PositiveFrame, FrameEnergy F c' (sourceRegularization CX C0 R) B'.val ≤
          FrameEnergy F c' (sourceRegularization CX C0 R) D.val) ∧
        ‖B₀.val⁻¹ * B'.val - 1‖ ≤ Kcmp / Real.sqrt (sourceRegularization CX C0 R) *
          physicalEuclideanNorm (B₀.val⁻¹ *ᵥ (c' - c)) ∧
        ‖B₀.val⁻¹ * B'.val‖ ≤ 7 / 4 ∧ ‖(B₀.val⁻¹ * B'.val)⁻¹‖ ≤ 7 / 4 := by
  obtain ⟨K, hK, hlift⟩ := exists_source_horizontal_minimizingFrame_with_bound k
    (convexHull ℝ X) (isBounded_convexHull.mpr hX) CX C0 hCX hC0
  refine ⟨1 / (8 * K), 4 * K, by positivity, by positivity, ?_⟩
  intro R hR F hF c hc c' hc' B₀ hmin hsmall
  let lam := sourceRegularization CX C0 R
  have hlam : 0 < lam := sourceRegularization_pos CX C0 R hCX hC0 hR
  have hsqrt : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  let u : PhysicalSpace := B₀.val⁻¹ *ᵥ (c' - c)
  let q : ℝ := K / Real.sqrt lam * physicalEuclideanNorm u
  have hq : 0 ≤ q := mul_nonneg (div_nonneg hK.le hsqrt.le) (physicalEuclideanNorm_nonneg u)
  have hqsmall : q ≤ 1 / 8 := by
    calc
      q ≤ K / Real.sqrt lam * ((1 / (8 * K)) * Real.sqrt lam) :=
        mul_le_mul_of_nonneg_left hsmall (div_nonneg hK.le hsqrt.le)
      _ = 1 / 8 := by field_simp; ring
  let cp : ℝ → PhysicalSpace := fun t => c + t • (c' - c)
  have hcp (t : ℝ) : HasDerivAt cp (c' - c) t := by
    simpa [cp] using ((hasDerivAt_id t).smul_const (c' - c)).const_add c
  have hcp0 : cp 0 = c := by simp [cp]
  have hcp1 : cp 1 = c' := by simp [cp]
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : cp t ∈ convexHull ℝ X := by
    apply segment_subset_convexHull hc hc'
    rw [segment_eq_image']
    exact ⟨t, ht, rfl⟩
  obtain ⟨a, b, ha, hb, _, B, hB0, _, hB⟩ :=
    hlift R hR F hF cp univ isOpen_univ (subset_univ _)
      ((show ContDiff ℝ ∞ cp from contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn) B₀
      (by simpa only [hcp0] using hmin)
  have hinside {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t ∈ Ioo a b :=
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  let A : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun t => B₀.val⁻¹ * B t
  have hA0 : A 0 = 1 := by rw [show A 0 = B₀.val⁻¹ * B 0 from rfl, hB0]; exact relativeFrame_initial B₀
  have hunit (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : IsUnit (A t) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [show A t = B₀.val⁻¹ * B t from rfl, Matrix.det_mul, Matrix.det_nonsing_inv]
    simpa only [Ring.inverse_eq_inv] using
      (isUnit_iff_ne_zero.mpr B₀.property.ne').inv.mul
        (isUnit_iff_ne_zero.mpr (hB t (hinside ht)).1.ne')
  have hBu : B₀.val *ᵥ u = c' - c := by
    rw [show u = B₀.val⁻¹ *ᵥ (c' - c) from rfl, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr B₀.property.ne'), Matrix.one_mulVec]
  have hgen (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∃ S : Matrix (Fin 3) (Fin 3) ℝ, HasDerivAt A (A t * S) t ∧ ‖S‖ ≤ q * ‖(A t)⁻¹‖ := by
    obtain ⟨hp, _, S, hd, hs⟩ := hB t (hinside ht)
    refine ⟨S.val, hasDerivAt_relativeFrame B₀ hd, ?_⟩
    have hv : (B t)⁻¹ *ᵥ deriv cp t = (A t)⁻¹ *ᵥ u := by
      rw [(hcp t).deriv, ← hBu]
      exact relativeFrame_normalized_velocity B₀ ⟨B t, hp⟩ u
    calc
      ‖S.val‖ ≤ matrixFullHSNorm S.val := matrix_opNorm_le_fullHS S.val
      _ ≤ K / Real.sqrt lam * physicalEuclideanNorm ((B t)⁻¹ *ᵥ deriv cp t) := hs (hpath t ht)
      _ = K / Real.sqrt lam * physicalEuclideanNorm ((A t)⁻¹ *ᵥ u) := by rw [hv]
      _ ≤ K / Real.sqrt lam * (‖(A t)⁻¹‖ * physicalEuclideanNorm u) :=
        mul_le_mul_of_nonneg_left (physicalEuclideanNorm_mulVec_le_opNorm _ _)
          (div_nonneg hK.le hsqrt.le)
      _ = q * ‖(A t)⁻¹‖ := by dsimp [q]; ring
  obtain ⟨hAn, hAin, hdiff, _⟩ := relativeFrame_bootstrap A q hq hqsmall hA0 hunit hgen 1 ⟨by norm_num, le_rfl⟩
  refine ⟨⟨B 1, (hB 1 (hinside ⟨by norm_num, le_rfl⟩)).1⟩, ?_, ?_, hAn, hAin⟩
  · simpa only [hcp1] using (hB 1 (hinside ⟨by norm_num, le_rfl⟩)).2.1
  · calc
      ‖B₀.val⁻¹ * B 1 - 1‖ ≤ 4 * q * 1 := hdiff
      _ = (4 * K) / Real.sqrt lam * physicalEuclideanNorm u := by dsimp [q]; ring

end PaperI
