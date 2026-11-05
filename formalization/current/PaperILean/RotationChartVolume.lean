import PaperILean.RotationChartTranslation
import Mathlib.MeasureTheory.Function.Jacobian

/-! I331 prerequisite: a locally translation-invariant coordinate measure with
the actual product Lebesgue reference measure. This auxiliary measure lives on
PhysicalSpace; it is not asserted to be the normalized Haar measure on SO(3). -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix Matrix.L2OpNorm
namespace PaperI

theorem physicalMeasure_isAddHaarMeasure : physicalMeasure.IsAddHaarMeasure := by
  rw [physicalMeasure_eq_volume]
  infer_instance

attribute [instance] physicalMeasure_isAddHaarMeasure

def rotationChartVolume : Measure PhysicalSpace :=
  physicalMeasure.withDensity (fun x => ENNReal.ofReal (rotationChartJacobian x))

theorem rotationChartJacobian_ofReal_measurable :
    Measurable (fun x => ENNReal.ofReal (rotationChartJacobian x)) :=
  rotationChartJacobian_continuous.measurable.ennreal_ofReal

theorem rotationChartVolume_apply (A : Set PhysicalSpace) (hA : MeasurableSet A) :
    rotationChartVolume A = ∫⁻ x in A, ENNReal.ofReal (rotationChartJacobian x) ∂physicalMeasure :=
  withDensity_apply _ hA

theorem rotationChartLeftTranslation_image_measurable (g : rotationGroup3)
    (A : Set PhysicalSpace) (hA : MeasurableSet A) (hsub : A ⊆ rotationChartTranslationSource g) :
    MeasurableSet (rotationChartLeftTranslation g '' A) :=
  measurable_image_of_fderivWithin hA
    (fun x hx => (rotationChartLeftTranslation_hasStrictFDerivAt g x (hsub hx)).hasFDerivAt.hasFDerivWithinAt)
    ((rotationChartLeftTranslation_injOn g).mono hsub)

theorem rotationChartJacobian_ofReal_translation (g : rotationGroup3) (x : PhysicalSpace)
    (hx : x ∈ rotationChartTranslationSource g) :
    ENNReal.ofReal |(rotationChartTranslationDifferential g x).toLinearMap.det| *
      ENNReal.ofReal (rotationChartJacobian (rotationChartLeftTranslation g x)) =
        ENNReal.ofReal (rotationChartJacobian x) := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm, rotationChartJacobian_translation g x hx]

theorem rotationChartVolume_translation (g : rotationGroup3) (A : Set PhysicalSpace)
    (hA : MeasurableSet A) (hsub : A ⊆ rotationChartTranslationSource g) :
    rotationChartVolume (rotationChartLeftTranslation g '' A) = rotationChartVolume A := by
  rw [rotationChartVolume_apply _ (rotationChartLeftTranslation_image_measurable g A hA hsub),
    rotationChartVolume_apply A hA]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul physicalMeasure hA
    (fun x hx => (rotationChartLeftTranslation_hasStrictFDerivAt g x (hsub hx)).hasFDerivAt.hasFDerivWithinAt)
    ((rotationChartLeftTranslation_injOn g).mono hsub)
    (fun x => ENNReal.ofReal (rotationChartJacobian x))
  rw [hcv]
  apply setLIntegral_congr_fun hA
  exact Filter.Eventually.of_forall (fun x hx => rotationChartJacobian_ofReal_translation g x (hsub hx))

theorem rotationChartVolume_uniform_core_bounds :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ A : Set PhysicalSpace, MeasurableSet A →
      A ⊆ rotationChartCore →
        ENNReal.ofReal c * physicalMeasure A ≤ rotationChartVolume A ∧
          rotationChartVolume A ≤ ENNReal.ofReal C * physicalMeasure A := by
  obtain ⟨c, C, hc, hcC, hb⟩ := rotationChartJacobian_uniform_bounds
  refine ⟨c, C, hc, hcC, ?_⟩
  intro A hA hsub
  rw [rotationChartVolume_apply A hA]
  constructor
  · calc
      ENNReal.ofReal c * physicalMeasure A = ∫⁻ _ in A, ENNReal.ofReal c ∂physicalMeasure := by simp
      _ ≤ _ := setLIntegral_mono' hA (fun x hx => ENNReal.ofReal_le_ofReal (hb x (hsub hx)).1)
  · calc
      _ ≤ ∫⁻ _ in A, ENNReal.ofReal C ∂physicalMeasure :=
        setLIntegral_mono' hA (fun x hx => ENNReal.ofReal_le_ofReal (hb x (hsub hx)).2)
      _ = ENNReal.ofReal C * physicalMeasure A := by simp

theorem rotationChartVolume_uniform_source_bounds :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i),
      ∀ t : ℝ, t < 1/10 → ∀ A : Set PhysicalSpace, MeasurableSet A →
        A ⊆ skewCoordinateBall e ((10/9)*t) →
          ENNReal.ofReal c * physicalMeasure A ≤ rotationChartVolume A ∧
            rotationChartVolume A ≤ ENNReal.ofReal C * physicalMeasure A := by
  obtain ⟨c, C, hc, hcC, hb⟩ := rotationChartVolume_uniform_core_bounds
  exact ⟨c, C, hc, hcC, fun e he t ht A hA hsub =>
    hb A hA (hsub.trans (skewCoordinateBall_subset_chartCore e he t ht))⟩

theorem rotationChartVolume_core_lt_top : rotationChartVolume rotationChartCore < ⊤ := by
  obtain ⟨c, C, hc, hcC, hb⟩ := rotationChartVolume_uniform_core_bounds
  have h := (hb rotationChartCore rotationChartCore_isCompact.isClosed.measurableSet
    (Set.Subset.refl _)).2
  exact h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    rotationChartCore_isCompact.measure_lt_top)

theorem rotationChartVolume_pos_of_physical_pos (A : Set PhysicalSpace)
    (hA : MeasurableSet A) (hsub : A ⊆ rotationChartCore) (hpos : 0 < physicalMeasure A) :
    0 < rotationChartVolume A := by
  obtain ⟨c, C, hc, hcC, hb⟩ := rotationChartVolume_uniform_core_bounds
  exact (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hc).ne' hpos.ne').trans_le (hb A hA hsub).1

end PaperI
