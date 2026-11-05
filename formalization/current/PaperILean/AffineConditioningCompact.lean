import PaperILean.AffineFieldPolynomial
import PaperILean.StoppedSpectralMinimum
import PaperILean.RankOnePositivity

/-! I3251[578,732): the actual stopped-state/full-field family has an attained
positive minimum, with a positive bound on every bounded parameter interval.
This module does not assert the unbounded-parameter power lower bound. -/

noncomputable section
open Matrix
namespace PaperI.AffineConditioning

def fieldSphere : Set (FieldIndex → ℝ) := {f | fieldNorm f = 1}

theorem isCompact_fieldSphere : IsCompact fieldSphere := by
  let e := (WithLp.linearEquiv 2 ℝ (FieldIndex → ℝ)).symm.toContinuousLinearEquiv.toHomeomorph
  have h := e.isCompact_preimage.mpr
    (isCompact_sphere (0 : EuclideanSpace ℝ FieldIndex) 1)
  change IsCompact {f | dist ((WithLp.linearEquiv 2 ℝ (FieldIndex → ℝ)).symm f) 0 = 1} at h
  simpa only [dist_zero_right, ← coordinateL2Norm_eq_norm, fieldSphere, fieldNorm] using h

theorem fieldSphere_nonempty : fieldSphere.Nonempty := by
  refine ⟨Pi.single (0, 0) (1 : ℝ), ?_⟩
  simp [fieldSphere, fieldNorm, coordinateL2Norm, Pi.single_apply]

def conditioningFamily (k : ℕ) (R : ℝ) :
    Set (AugmentedState k × (FieldIndex → ℝ)) :=
  {z | AugmentedTranslationStopped R z.1 ∧ fieldNorm z.2 = 1}

theorem isCompact_conditioningFamily (k : ℕ) (R : ℝ) :
    IsCompact (conditioningFamily k R) :=
  (isCompact_augmentedTranslationStopped k R).prod isCompact_fieldSphere

theorem conditioningFamily_nonempty (k : ℕ) (R : ℝ) (hR : 2 ≤ R) :
    (conditioningFamily k R).Nonempty :=
  (augmentedTranslationStopped_nonempty k R hR).prod fieldSphere_nonempty

theorem gap_pos (k : ℕ) (hk : 2 ≤ k) (R : ℝ) (hR : 2 ≤ R)
    (S : AugmentedState k) (f : FieldIndex → ℝ)
    (hS : AugmentedTranslationStopped R S) (hf : fieldNorm f = 1) :
    0 < gap k S f := by
  have hRpos : 0 < R := by linarith
  have hstop : ∀ u : PhysicalSpace,
      (R⁻¹) ^ 2 * physicalEuclideanNorm u ^ 2 ≤
        coefficientEuclideanNorm (directionalCoefficientMap k u S.1) ^ 2 +
          physicalEuclideanNorm (S.2.2 *ᵥ u) ^ 2 := by
    intro u
    simpa only [_root_.zpow_neg, zpow_natCast, inv_pow] using hS.2 u
  have hunit : RankOneAffineMatrix.affineFieldFrobenius
      (fieldTranslation f) (fieldLinear f) = 1 :=
    (fieldNorm_eq_frobenius f).symm.trans hf
  simpa only [gap, actualAction, fieldMatrix_reconstruction] using
    RankOnePositivity.middle_cutoff_exact_positivity_stage hk S.1 S.2
      R⁻¹ (inv_pos.mpr hRpos) hstop (fieldTranslation f) (fieldLinear f) hunit

attribute [local irreducible] gap

def minimum (k : ℕ) (R : ℝ) : ℝ :=
  if 2 ≤ R then
    sInf ((fun z : AugmentedState k × (FieldIndex → ℝ) => gap k z.1 z.2) ''
      conditioningFamily k R)
  else 0

theorem minimum_spec (k : ℕ) (R : ℝ) (hR : 2 ≤ R) :
    ∃ S : AugmentedState k, ∃ f : FieldIndex → ℝ,
      AugmentedTranslationStopped R S ∧ fieldNorm f = 1 ∧
        minimum k R = gap k S f ∧
        ∀ T : AugmentedState k, ∀ g : FieldIndex → ℝ,
          AugmentedTranslationStopped R T → fieldNorm g = 1 →
            minimum k R ≤ gap k T g := by
  obtain ⟨z, hz, hmin⟩ := (isCompact_conditioningFamily k R).exists_isMinOn
    (f := fun z : AugmentedState k × (FieldIndex → ℝ) => gap k z.1 z.2)
    (conditioningFamily_nonempty k R hR) (continuous_gap k).continuousOn
  have he : minimum k R = gap k z.1 z.2 := by
    rw [minimum, if_pos hR]
    exact csInf_image_eq_of_minimizer
      (f := fun y : AugmentedState k × (FieldIndex → ℝ) => gap k y.1 y.2)
      (x := z) hz (fun y hy => hmin hy)
  refine ⟨z.1, z.2, hz.1, hz.2, he, ?_⟩
  intro T g hT hg
  calc
    minimum k R = gap k z.1 z.2 := he
    _ ≤ gap k T g := hmin (show (T, g) ∈ conditioningFamily k R from ⟨hT, hg⟩)

theorem minimum_eq_iff (k : ℕ) (R t : ℝ) (hR : 2 ≤ R) :
    t = minimum k R ↔
      ∃ S : AugmentedState k, ∃ f : FieldIndex → ℝ,
        AugmentedTranslationStopped R S ∧ fieldNorm f = 1 ∧ t = gap k S f ∧
          ∀ T : AugmentedState k, ∀ g : FieldIndex → ℝ,
            AugmentedTranslationStopped R T → fieldNorm g = 1 → t ≤ gap k T g := by
  obtain ⟨S, f, hS, hf, he, hmin⟩ := minimum_spec k R hR
  constructor
  · rintro rfl
    exact ⟨S, f, hS, hf, he, hmin⟩
  · rintro ⟨T, g, hT, hg, ht, hleast⟩
    exact le_antisymm ((hleast S f hS hf).trans_eq he.symm)
      ((hmin T g hT hg).trans_eq ht.symm)

theorem minimum_pos (k : ℕ) (hk : 2 ≤ k) (R : ℝ) (hR : 2 ≤ R) :
    0 < minimum k R := by
  obtain ⟨S, f, hS, hf, he, _⟩ := minimum_spec k R hR
  rw [he]
  exact gap_pos k hk R hR S f hS hf

theorem minimum_le (k : ℕ) (R : ℝ) (hR : 2 ≤ R)
    (S : AugmentedState k) (f : FieldIndex → ℝ)
    (hS : AugmentedTranslationStopped R S) (hf : fieldNorm f = 1) :
    minimum k R ≤ gap k S f := by
  obtain ⟨_, _, _, _, _, hmin⟩ := minimum_spec k R hR
  exact hmin S f hS hf

theorem bounded_parameter_lower (k : ℕ) (hk : 2 ≤ k) (T : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, 2 ≤ R → R ≤ T → c ≤ minimum k R := by
  let K : Set ((ℝ × AugmentedState k) × (FieldIndex → ℝ)) :=
    {z | 2 ≤ z.1 ∧ z.1 ≤ T ∧ AugmentedTranslationStopped z.1 z.2} ×ˢ fieldSphere
  have hK : IsCompact K :=
    (isCompact_augmentedStoppedBoundedFamily k T).prod isCompact_fieldSphere
  have hcont : Continuous (fun z : (ℝ × AugmentedState k) × (FieldIndex → ℝ) =>
      gap k z.1.2 z.2) :=
    (continuous_gap k).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨c, hc, hbound⟩ := exists_pos_le_on_compact hK hcont.continuousOn
    (fun z hz => gap_pos k hk z.1.1 hz.1.1 z.1.2 z.2 hz.1.2.2 hz.2)
  refine ⟨c, hc, fun R hR hRT => ?_⟩
  obtain ⟨S, f, hS, hf, he, _⟩ := minimum_spec k R hR
  exact (hbound ((R, S), f) (show ((R, S), f) ∈ K from ⟨⟨hR, hRT, hS⟩, hf⟩)).trans_eq he.symm

end PaperI.AffineConditioning
