import PaperILean.DirectionalCoefficientBounds

/-! Normalized center stability of the augmented translation quadratic form.
The physical term is part of the definition. The lower-bound implication
explicitly receives its source lower bound; it does not prove that a minimizing
frame supplies either that bound or the bounded-jet window.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

theorem coefficientEuclideanNorm_nonneg {k : ℕ} (F : CoefficientSpace k) :
    0 ≤ coefficientEuclideanNorm F := Real.sqrt_nonneg _

theorem coefficientEuclideanNorm_sub_le {k : ℕ} (F G : CoefficientSpace k) :
    coefficientEuclideanNorm F ≤ coefficientEuclideanNorm (F - G) +
      coefficientEuclideanNorm G := by
  simp only [coefficientEuclideanNorm_eq_norm, map_sub]
  simpa only [sub_add_cancel] using norm_add_le
    ((WithLp.linearEquiv 2 ℝ (CoefficientSpace k)).symm F -
      (WithLp.linearEquiv 2 ℝ (CoefficientSpace k)).symm G)
    ((WithLp.linearEquiv 2 ℝ (CoefficientSpace k)).symm G)

theorem coefficientEuclideanNorm_sq_difference_le {k : ℕ} (F G : CoefficientSpace k) :
    |(coefficientEuclideanNorm F) ^ 2 - (coefficientEuclideanNorm G) ^ 2| ≤
      coefficientEuclideanNorm (F - G) *
        (coefficientEuclideanNorm F + coefficientEuclideanNorm G) := by
  have h : |coefficientEuclideanNorm F - coefficientEuclideanNorm G| ≤
      coefficientEuclideanNorm (F - G) := by
    simp only [coefficientEuclideanNorm_eq_norm, map_sub]
    exact abs_norm_sub_norm_le _ _
  rw [show (coefficientEuclideanNorm F) ^ 2 - (coefficientEuclideanNorm G) ^ 2 =
    (coefficientEuclideanNorm F - coefficientEuclideanNorm G) *
      (coefficientEuclideanNorm F + coefficientEuclideanNorm G) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (coefficientEuclideanNorm_nonneg F)
      (coefficientEuclideanNorm_nonneg G))]
  exact mul_le_mul_of_nonneg_right h
    (add_nonneg (coefficientEuclideanNorm_nonneg F) (coefficientEuclideanNorm_nonneg G))

def augmentedTranslationQuadratic {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) : ℝ :=
  (coefficientEuclideanNorm
    (directionalCoefficientMap k u (affineCoefficientMap k c B F))) ^ 2 +
      (physicalEuclideanNorm (B *ᵥ u)) ^ 2

theorem augmentedTranslationQuadratic_nonneg {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) :
    0 ≤ augmentedTranslationQuadratic F c B u := by
  unfold augmentedTranslationQuadratic
  positivity

def translationStopVariationConstant (k : ℕ) : ℝ :=
  (directionalCoefficientConstant k) ^ 2 * (k : ℝ) ^ 2 * (2 + (k : ℝ) ^ 2)

theorem translationStopVariationConstant_nonneg (k : ℕ) :
    0 ≤ translationStopVariationConstant k := by
  unfold translationStopVariationConstant
  positivity

theorem translationStop_center_variation_bound {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (M : ℝ)
    (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M)
    (h : PhysicalSpace) (hh : physicalEuclideanNorm h ≤ 1) (u : PhysicalSpace) :
    |augmentedTranslationQuadratic F (c + B *ᵥ h) B u -
      augmentedTranslationQuadratic F c B u| ≤
        translationStopVariationConstant k * M ^ 2 * physicalEuclideanNorm h *
          (physicalEuclideanNorm u) ^ 2 := by
  let A := directionalCoefficientMap k u (affineCoefficientMap k (c + B *ᵥ h) B F)
  let G := directionalCoefficientMap k u (affineCoefficientMap k c B F)
  let C := directionalCoefficientConstant k
  have hC : 0 ≤ C := directionalCoefficientConstant_nonneg k
  have hM0 := boundedJet_window_nonneg F c B M hM
  have hH0 := physicalEuclideanNorm_nonneg h
  have hU0 := physicalEuclideanNorm_nonneg u
  have hG : coefficientEuclideanNorm G ≤ C * M * physicalEuclideanNorm u :=
    affine_directionalCoefficient_norm_bound F c B M hM u
  have hd : coefficientEuclideanNorm (A - G) ≤
      C * ((k : ℝ) ^ 2 * M * physicalEuclideanNorm h) * physicalEuclideanNorm u :=
    affine_directionalCoefficient_difference_bound F c B M hM h hh u
  have hd' : coefficientEuclideanNorm (A - G) ≤
      C * ((k : ℝ) ^ 2 * M) * physicalEuclideanNorm u := by
    apply hd.trans
    have hb : (k : ℝ) ^ 2 * M * physicalEuclideanNorm h ≤ (k : ℝ) ^ 2 * M :=
      mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) hM0) hh
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hC) hU0
  have hA : coefficientEuclideanNorm A ≤
      C * (1 + (k : ℝ) ^ 2) * M * physicalEuclideanNorm u := by
    calc
      coefficientEuclideanNorm A ≤ coefficientEuclideanNorm (A - G) +
          coefficientEuclideanNorm G := coefficientEuclideanNorm_sub_le A G
      _ ≤ C * ((k : ℝ) ^ 2 * M) * physicalEuclideanNorm u +
          C * M * physicalEuclideanNorm u := add_le_add hd' hG
      _ = _ := by ring
  have hsum : coefficientEuclideanNorm A + coefficientEuclideanNorm G ≤
      C * (2 + (k : ℝ) ^ 2) * M * physicalEuclideanNorm u := by
    exact (add_le_add hA hG).trans_eq (by ring)
  have hprod := mul_le_mul hd hsum
    (add_nonneg (coefficientEuclideanNorm_nonneg A) (coefficientEuclideanNorm_nonneg G))
    (by positivity : 0 ≤ C * ((k : ℝ) ^ 2 * M * physicalEuclideanNorm h) *
      physicalEuclideanNorm u)
  have hq : augmentedTranslationQuadratic F (c + B *ᵥ h) B u -
      augmentedTranslationQuadratic F c B u =
        (coefficientEuclideanNorm A) ^ 2 - (coefficientEuclideanNorm G) ^ 2 := by
    unfold augmentedTranslationQuadratic
    dsimp [A, G]
    ring
  rw [hq]
  apply (coefficientEuclideanNorm_sq_difference_le A G).trans
  exact hprod.trans_eq (by unfold translationStopVariationConstant; dsimp [C]; ring)

theorem translationStop_center_variation (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (M : ℝ) (F : CoefficientSpace k) (c : PhysicalSpace)
      (B : Matrix (Fin 3) (Fin 3) ℝ) (h u : PhysicalSpace),
      (∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M) →
      physicalEuclideanNorm h ≤ 1 →
      |augmentedTranslationQuadratic F (c + B *ᵥ h) B u -
        augmentedTranslationQuadratic F c B u| ≤
          D * M ^ 2 * physicalEuclideanNorm h * (physicalEuclideanNorm u) ^ 2 := by
  refine ⟨translationStopVariationConstant k, translationStopVariationConstant_nonneg k, ?_⟩
  intro M F c B h u hM hh
  exact translationStop_center_variation_bound F c B M hM h hh u

theorem translationStop_center_stability {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (M : ℝ)
    (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M)
    (h : PhysicalSpace) (hh : physicalEuclideanNorm h ≤ 1) (a : ℝ) (_ha : 0 < a)
    (hsource : ∀ u : PhysicalSpace,
      a * (physicalEuclideanNorm u) ^ 2 ≤ augmentedTranslationQuadratic F c B u)
    (hsmall : translationStopVariationConstant k * M ^ 2 * physicalEuclideanNorm h ≤ a / 2)
    (u : PhysicalSpace) :
    (a / 2) * (physicalEuclideanNorm u) ^ 2 ≤
      augmentedTranslationQuadratic F (c + B *ᵥ h) B u := by
  have hv := (abs_le.mp (translationStop_center_variation_bound F c B M hM h hh u)).1
  have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (physicalEuclideanNorm u))
  have hl := hsource u
  linarith

/-- The radius is chosen before F,c,B,h,u. Zero D_k or M requires no special
case, because only the strictly positive denominator 1 + D_k M^2 is used. -/
theorem translationStop_uniform_radius (k : ℕ) (M a : ℝ) (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (F : CoefficientSpace k) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ),
      (∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M) →
      (∀ u : PhysicalSpace,
        a * (physicalEuclideanNorm u) ^ 2 ≤ augmentedTranslationQuadratic F c B u) →
      ∀ h : PhysicalSpace, physicalEuclideanNorm h ≤ δ → ∀ u : PhysicalSpace,
        (a / 2) * (physicalEuclideanNorm u) ^ 2 ≤
          augmentedTranslationQuadratic F (c + B *ᵥ h) B u := by
  let L := translationStopVariationConstant k * M ^ 2
  have hL : 0 ≤ L := mul_nonneg (translationStopVariationConstant_nonneg k) (sq_nonneg M)
  have hden : 0 < L + 1 := by linarith
  refine ⟨min 1 ((a / 2) / (L + 1)), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  intro F c B hM hsource h hh u
  have hh1 : physicalEuclideanNorm h ≤ 1 := hh.trans (min_le_left _ _)
  have hhdiv : physicalEuclideanNorm h ≤ (a / 2) / (L + 1) :=
    hh.trans (min_le_right _ _)
  have hs := (le_div_iff₀ hden).mp hhdiv
  have hH0 := physicalEuclideanNorm_nonneg h
  have hsmall : L * physicalEuclideanNorm h ≤ a / 2 := by nlinarith
  exact translationStop_center_stability F c B M hM h hh1 a ha hsource hsmall u

end PaperI
