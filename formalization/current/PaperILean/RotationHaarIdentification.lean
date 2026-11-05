import PaperILean.RotationInvariantVolume

/-! I331: identify the existing normalized Haar measure with the constructed
coordinate volume. No Haar measure, chart, reference measure or source parameter
is redefined. The positive scalar and all comparison constants are chosen first. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix Matrix.L2OpNorm
namespace PaperI

theorem rotationInvariantVolume_eq_smul_haar :
    rotationInvariantVolume = rotationInvariantVolume univ • rotationHaarMeasure :=
  Measure.haarMeasure_unique rotationInvariantVolume rotationGroupPositiveCompact

def rotationHaarChartScale : ℝ := (rotationInvariantVolume univ).toReal⁻¹

theorem rotationHaarChartScale_pos : 0 < rotationHaarChartScale :=
  inv_pos.mpr (ENNReal.toReal_pos rotationInvariantVolume_univ_positive.ne'
    rotationInvariantVolume_univ_finite.ne)

theorem rotationHaarChartScale_ofReal :
    ENNReal.ofReal rotationHaarChartScale = (rotationInvariantVolume univ)⁻¹ := by
  rw [rotationHaarChartScale, ENNReal.ofReal_inv_of_pos
    (ENNReal.toReal_pos rotationInvariantVolume_univ_positive.ne'
      rotationInvariantVolume_univ_finite.ne),
    ENNReal.ofReal_toReal rotationInvariantVolume_univ_finite.ne]

theorem rotationHaarMeasure_chart_identity (A : Set PhysicalSpace)
    (hA : MeasurableSet A) (hsub : A ⊆ rotationChartSource) :
    rotationHaarMeasure (rotationCoordinateExp '' A) =
      ENNReal.ofReal rotationHaarChartScale * rotationChartVolume A := by
  have him : rotationInvariantVolume (rotationCoordinateExp '' A) = rotationChartVolume A := by
    simpa only [one_mul] using rotationInvariantVolume_image 1 A hA hsub
  have hm : rotationChartVolume A = rotationInvariantVolume univ *
      rotationHaarMeasure (rotationCoordinateExp '' A) := by
    apply him.symm.trans
    simpa only [Measure.smul_apply, smul_eq_mul] using
      congrArg (fun μ : Measure rotationGroup3 => μ (rotationCoordinateExp '' A))
        rotationInvariantVolume_eq_smul_haar
  rw [hm, rotationHaarChartScale_ofReal]
  exact (ENNReal.inv_mul_cancel_left rotationInvariantVolume_univ_positive.ne'
    rotationInvariantVolume_univ_finite.ne).symm

theorem rotationHaarMeasure_exists_chart_scale :
    ∃ a : ℝ, 0 < a ∧ ∀ A : Set PhysicalSpace, MeasurableSet A → A ⊆ rotationChartSource →
      rotationHaarMeasure (rotationCoordinateExp '' A) = ENNReal.ofReal a * rotationChartVolume A :=
  ⟨rotationHaarChartScale, rotationHaarChartScale_pos, rotationHaarMeasure_chart_identity⟩

theorem rotationHaarMeasure_uniform_core_bounds :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ A : Set PhysicalSpace, MeasurableSet A →
      A ⊆ rotationChartCore →
        ENNReal.ofReal c * physicalMeasure A ≤ rotationHaarMeasure (rotationCoordinateExp '' A) ∧
          rotationHaarMeasure (rotationCoordinateExp '' A) ≤ ENNReal.ofReal C * physicalMeasure A := by
  obtain ⟨c, C, hc, hcC, hb⟩ := rotationChartVolume_uniform_core_bounds
  refine ⟨rotationHaarChartScale * c, rotationHaarChartScale * C,
    mul_pos rotationHaarChartScale_pos hc,
    mul_le_mul_of_nonneg_left hcC rotationHaarChartScale_pos.le, ?_⟩
  intro A hA hsub
  rw [rotationHaarMeasure_chart_identity A hA (hsub.trans rotationChartCore_subset_source),
    ENNReal.ofReal_mul rotationHaarChartScale_pos.le,
    ENNReal.ofReal_mul rotationHaarChartScale_pos.le]
  constructor
  · simpa only [mul_assoc] using mul_le_mul_left' (hb A hA hsub).1
      (ENNReal.ofReal rotationHaarChartScale)
  · simpa only [mul_assoc] using mul_le_mul_left' (hb A hA hsub).2
      (ENNReal.ofReal rotationHaarChartScale)

theorem rotationHaarMeasure_uniform_chart_bounds :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ A : Set PhysicalSpace, MeasurableSet A →
      A ⊆ rotationChartInner →
        ENNReal.ofReal c * physicalMeasure A ≤ rotationHaarMeasure (rotationCoordinateExp '' A) ∧
          rotationHaarMeasure (rotationCoordinateExp '' A) ≤ ENNReal.ofReal C * physicalMeasure A := by
  obtain ⟨c, C, hc, hcC, hb⟩ := rotationHaarMeasure_uniform_core_bounds
  exact ⟨c, C, hc, hcC, fun A hA hsub => hb A hA (hsub.trans rotationChartInner_subset_core)⟩

theorem rotationHaarMeasure_uniform_source_bounds :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i),
      ∀ t : ℝ, t < 1/10 → ∀ A : Set PhysicalSpace, MeasurableSet A →
        A ⊆ skewCoordinateBall e ((10/9)*t) →
          ENNReal.ofReal c * physicalMeasure A ≤ rotationHaarMeasure (rotationCoordinateExp '' A) ∧
            rotationHaarMeasure (rotationCoordinateExp '' A) ≤ ENNReal.ofReal C * physicalMeasure A := by
  obtain ⟨c, C, hc, hcC, hb⟩ := rotationHaarMeasure_uniform_core_bounds
  exact ⟨c, C, hc, hcC, fun e he t ht A hA hsub =>
    hb A hA (hsub.trans (skewCoordinateBall_subset_chartCore e he t ht))⟩

end PaperI
