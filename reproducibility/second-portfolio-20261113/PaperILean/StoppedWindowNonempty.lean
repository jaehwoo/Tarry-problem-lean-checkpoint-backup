import PaperILean.StoppedNormalCompactMinimum

/-! I602-605, I625-636 and I683: nonempty exact stopped windows and attainment
of the positive normal minimum. The witness uses degree-zero phase for any k;
no invertibility premise is imposed on arbitrary states. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

/-- A nonempty-window witness with zero phase and physical matrix P⁻¹ I. -/
def referenceAugmentedState (k : ℕ) (P : ℝ) : AugmentedState k :=
  (0, (0, P⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ)))

theorem referenceAugmentedState_norm_sq (k : ℕ) (P : ℝ) :
    augmentedStateNorm (referenceAugmentedState k P) ^ 2 = 3 * (P⁻¹) ^ 2 := by
  rw [augmentedStateNorm_sq]
  simp [referenceAugmentedState, coefficientEuclideanNorm, Fin.sum_univ_succ,
    Matrix.one_apply]

theorem referenceAugmentedState_translation_energy (k : ℕ) (P : ℝ)
    (h : PhysicalSpace) :
    coefficientEuclideanNorm (directionalCoefficientMap k h (referenceAugmentedState k P).1) ^ 2 +
      physicalEuclideanNorm ((referenceAugmentedState k P).2.2 *ᵥ h) ^ 2 =
        P ^ (-2 : ℤ) * physicalEuclideanNorm h ^ 2 := by
  simp [referenceAugmentedState, coefficientEuclideanNorm, Matrix.smul_mulVec_assoc,
    physicalEuclideanNorm, coordinateL2Norm_smul, mul_pow, sq_abs, inv_pow]
  left
  norm_cast

theorem referenceAugmentedState_stopped (k : ℕ) (P : ℝ) (hP : 2 ≤ P) :
    AugmentedTranslationStopped P (referenceAugmentedState k P) := by
  have hpos : 0 < P := by linarith
  have hi : P⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr (by linarith)
  have hi0 : 0 ≤ P⁻¹ := inv_nonneg.mpr hpos.le
  have hisq : (P⁻¹) ^ 2 ≤ 1 := pow_le_one₀ hi0 hi
  constructor
  · have hsq := referenceAugmentedState_norm_sq k P
    nlinarith [augmentedStateNorm_nonneg (referenceAugmentedState k P)]
  · intro h
    exact (referenceAugmentedState_translation_energy k P h).ge

theorem augmentedTranslationStopped_nonempty (k : ℕ) (P : ℝ) (hP : 2 ≤ P) :
    Set.Nonempty {S : AugmentedState k | AugmentedTranslationStopped P S} :=
  ⟨referenceAugmentedState k P, referenceAugmentedState_stopped k P hP⟩

/-- The actual positive normal minimum is attained for every source parameter. -/
theorem stopped_normalOrbit_minimum_attained (k : ℕ) (P : ℝ) (hP : 2 ≤ P) :
    ∃ S : AugmentedState k, AugmentedTranslationStopped P S ∧
      0 < normalOrbitSingularValues k S 2 ∧
      ∀ T : AugmentedState k, AugmentedTranslationStopped P T →
        normalOrbitSingularValues k S 2 ≤ normalOrbitSingularValues k T 2 := by
  obtain ⟨S, hS, hmin⟩ := (isCompact_augmentedTranslationStopped k P).exists_isMinOn
    (augmentedTranslationStopped_nonempty k P hP)
    (continuous_normalOrbit_leastSingularValue k).continuousOn
  exact ⟨S, hS, stopped_normalOrbit_last_singularValue_pos_of_two_le hP S hS,
    fun T hT => hmin hT⟩

end PaperI
