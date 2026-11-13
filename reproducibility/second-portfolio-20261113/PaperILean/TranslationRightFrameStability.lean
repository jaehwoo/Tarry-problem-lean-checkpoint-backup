import PaperILean.CoefficientFrameBounds

/-! Stability under a bounded invertible right-frame change. The source lower
bound is an explicit input; no minimizing-frame theorem is assumed as an axiom.
Euclidean bounds are on the actual WithLp 2 operator, never the Pi supremum norm.
Constants are chosen before the polynomial, center, frames and directions.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

theorem physicalEuclideanNorm_le_frame_inverse {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.det ≠ 0) (L : ℝ)
    (hInv : ∀ v : PhysicalSpace,
      physicalEuclideanNorm (A⁻¹ *ᵥ v) ≤ L * physicalEuclideanNorm v)
    (u : PhysicalSpace) :
    physicalEuclideanNorm u ≤ L * physicalEuclideanNorm (A *ᵥ u) := by
  have hi : A⁻¹ *ᵥ (A *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),
      Matrix.one_mulVec]
  simpa only [hi] using hInv (A *ᵥ u)

theorem augmentedTranslation_right_frame_comparison {k : ℕ}
    (F : CoefficientSpace k) (c : PhysicalSpace) (B A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.det ≠ 0) (K : ℝ) (hK : 0 ≤ K)
    (hPull : ∀ G : CoefficientSpace k,
      coefficientEuclideanNorm (affineCoefficientMap k 0 A⁻¹ G) ≤
        K * coefficientEuclideanNorm G) (u : PhysicalSpace) :
    augmentedTranslationQuadratic F c B (A *ᵥ u) ≤
      (1 + K ^ 2) * augmentedTranslationQuadratic F c (B * A) u := by
  have hb := hPull (directionalCoefficientMap k u (affineCoefficientMap k c (B * A) F))
  rw [directionalCoefficient_right_frame_inverse F c B A hA u] at hb
  have hs := (sq_le_sq₀ (coefficientEuclideanNorm_nonneg _)
    (mul_nonneg hK (coefficientEuclideanNorm_nonneg _))).mpr hb
  simp only [mul_pow] at hs
  unfold augmentedTranslationQuadratic
  rw [Matrix.mulVec_mulVec]
  nlinarith [sq_nonneg (coefficientEuclideanNorm
    (directionalCoefficientMap k u (affineCoefficientMap k c (B * A) F))),
    sq_nonneg (physicalEuclideanNorm ((B * A) *ᵥ u)), sq_nonneg K]

theorem augmentedTranslation_lower_bound_right_frame {k : ℕ}
    (F : CoefficientSpace k) (c : PhysicalSpace) (B A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.det ≠ 0) (L K a : ℝ) (hL : 1 ≤ L) (hK : 0 ≤ K) (ha : 0 < a)
    (hInv : ∀ v : PhysicalSpace,
      physicalEuclideanNorm (A⁻¹ *ᵥ v) ≤ L * physicalEuclideanNorm v)
    (hPull : ∀ G : CoefficientSpace k,
      coefficientEuclideanNorm (affineCoefficientMap k 0 A⁻¹ G) ≤
        K * coefficientEuclideanNorm G)
    (hsource : ∀ v : PhysicalSpace,
      a * (physicalEuclideanNorm v) ^ 2 ≤ augmentedTranslationQuadratic F c B v)
    (u : PhysicalSpace) :
    (a / (L ^ 2 * (1 + K ^ 2))) * (physicalEuclideanNorm u) ^ 2 ≤
      augmentedTranslationQuadratic F c (B * A) u := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hden : 0 < L ^ 2 * (1 + K ^ 2) := by positivity
  have hi := physicalEuclideanNorm_le_frame_inverse hA L hInv u
  have his := (sq_le_sq₀ (physicalEuclideanNorm_nonneg u)
    (mul_nonneg hL0 (physicalEuclideanNorm_nonneg (A *ᵥ u)))).mpr hi
  simp only [mul_pow] at his
  have hq := augmentedTranslation_right_frame_comparison F c B A hA K hK hPull u
  have hh : a * (physicalEuclideanNorm u) ^ 2 ≤
      (L ^ 2 * (1 + K ^ 2)) * augmentedTranslationQuadratic F c (B * A) u := by
    calc
      _ ≤ a * (L ^ 2 * (physicalEuclideanNorm (A *ᵥ u)) ^ 2) :=
        mul_le_mul_of_nonneg_left his ha.le
      _ = L ^ 2 * (a * (physicalEuclideanNorm (A *ᵥ u)) ^ 2) := by ring
      _ ≤ L ^ 2 * augmentedTranslationQuadratic F c B (A *ᵥ u) :=
        mul_le_mul_of_nonneg_left (hsource _) (sq_nonneg L)
      _ ≤ L ^ 2 * ((1 + K ^ 2) * augmentedTranslationQuadratic F c (B * A) u) :=
        mul_le_mul_of_nonneg_left hq (sq_nonneg L)
      _ = _ := by ring
  have hd : (a * (physicalEuclideanNorm u) ^ 2) / (L ^ 2 * (1 + K ^ 2)) ≤
      augmentedTranslationQuadratic F c (B * A) u :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hh)
  convert hd using 1; ring

/-- Uniform stability, with both bounds retained in the statement. The inverse
bound alone controls this lower estimate; the forward bound also controls the
higher-jet window needed for subsequent center translation. -/
theorem translationStop_bounded_right_frame_vector (k : ℕ) (L a : ℝ)
    (hL : 1 ≤ L) (ha : 0 < a) :
    ∃ a' : ℝ, 0 < a' ∧
      ∀ (F : CoefficientSpace k) (c : PhysicalSpace)
        (B A : Matrix (Fin 3) (Fin 3) ℝ),
      A.det ≠ 0 →
      (∀ v : PhysicalSpace, physicalEuclideanNorm (A *ᵥ v) ≤ L * physicalEuclideanNorm v) →
      (∀ v : PhysicalSpace, physicalEuclideanNorm (A⁻¹ *ᵥ v) ≤ L * physicalEuclideanNorm v) →
      (∀ v : PhysicalSpace,
        a * (physicalEuclideanNorm v) ^ 2 ≤ augmentedTranslationQuadratic F c B v) →
      ∀ u : PhysicalSpace,
        a' * (physicalEuclideanNorm u) ^ 2 ≤ augmentedTranslationQuadratic F c (B * A) u := by
  obtain ⟨K, hK, hPull⟩ := bounded_centeredCoefficient_pullback k L hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  refine ⟨a / (L ^ 2 * (1 + K ^ 2)), by positivity, ?_⟩
  intro F c B A hA _hForward hInv hsource u
  exact augmentedTranslation_lower_bound_right_frame F c B A hA L K a hL
    (zero_le_one.trans hK) ha hInv (fun G => hPull A⁻¹ G hInv) hsource u

/-- Source contract at Paper I lines169-176 and265. The Euclidean operator-norm
formulation is equivalent to the checked vector bounds. No B inverse is used,
so the implication includes every source GL3 frame as a special case. -/
theorem translationStop_bounded_right_frame (k : ℕ) (_hk : 2 ≤ k) (L a : ℝ)
    (hL : 1 ≤ L) (ha : 0 < a) :
    ∃ a' : ℝ, 0 < a' ∧
      ∀ (F : CoefficientSpace k) (c : PhysicalSpace)
        (B A : Matrix (Fin 3) (Fin 3) ℝ),
      A.det ≠ 0 → euclideanFrameOperatorNorm A ≤ L →
      euclideanFrameOperatorNorm A⁻¹ ≤ L →
      (∀ v : PhysicalSpace,
        a * (physicalEuclideanNorm v) ^ 2 ≤ augmentedTranslationQuadratic F c B v) →
      ∀ u : PhysicalSpace,
        a' * (physicalEuclideanNorm u) ^ 2 ≤ augmentedTranslationQuadratic F c (B * A) u := by
  obtain ⟨a', ha', hs⟩ := translationStop_bounded_right_frame_vector k L a hL ha
  refine ⟨a', ha', ?_⟩
  intro F c B A hA hForward hInv hsource u
  exact hs F c B A hA
    ((euclideanFrameOperatorNorm_le_iff A L (zero_le_one.trans hL)).mp hForward)
    ((euclideanFrameOperatorNorm_le_iff A⁻¹ L (zero_le_one.trans hL)).mp hInv) hsource u

/-- Composition of the source's two stability assertions. The positive
constant is chosen before M; the radius is chosen before F,c,B,A,h,u.
Both minimizing-frame window and stopping bound remain explicit inputs. -/
theorem translationStop_bounded_right_frame_uniform_radius (k : ℕ) (hk : 2 ≤ k)
    (L a : ℝ) (hL : 1 ≤ L) (ha : 0 < a) :
    ∃ a' : ℝ, 0 < a' ∧ ∀ M : ℝ,
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
        ∀ (F : CoefficientSpace k) (c : PhysicalSpace)
          (B A : Matrix (Fin 3) (Fin 3) ℝ),
        A.det ≠ 0 → euclideanFrameOperatorNorm A ≤ L →
        euclideanFrameOperatorNorm A⁻¹ ≤ L →
        (∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M) →
        (∀ v : PhysicalSpace,
          a * (physicalEuclideanNorm v) ^ 2 ≤ augmentedTranslationQuadratic F c B v) →
        ∀ h : PhysicalSpace, physicalEuclideanNorm h ≤ δ → ∀ u : PhysicalSpace,
          (a' / 2) * (physicalEuclideanNorm u) ^ 2 ≤
            augmentedTranslationQuadratic F (c + (B * A) *ᵥ h) (B * A) u := by
  obtain ⟨a', ha', hs⟩ := translationStop_bounded_right_frame k hk L a hL ha
  refine ⟨a', ha', ?_⟩
  intro M
  obtain ⟨δ, hδ, hδ1, hcenter⟩ := translationStop_uniform_radius k ((9 * L) ^ k * M) a' ha'
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro F c B A hA hForward hInv hM hsource h hh u
  exact hcenter F c (B * A)
    (boundedJet_window_right_frame F c B A L hL
      ((euclideanFrameOperatorNorm_le_iff A L (zero_le_one.trans hL)).mp hForward) M hM)
    (hs F c B A hA hForward hInv hsource) h hh u

end PaperI
