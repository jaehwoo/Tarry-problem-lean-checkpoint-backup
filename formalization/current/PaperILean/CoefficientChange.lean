import PaperILean.AffinePullback
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Fixed-frame coefficient substitution with the actual linear determinant.
The equality of that determinant with the manuscript's chi-character is
not assumed in these completed measure-change lemmas. -/

open scoped ENNReal
open MeasureTheory

noncomputable section
namespace PaperI

theorem coefficientMeasure_eq_volume (k : ℕ) :
    coefficientMeasure k = (volume : Measure (CoefficientSpace k)) := rfl

theorem affineCoefficientMap_det_ne_zero (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) :
    LinearMap.det (affineCoefficientMap k c B) ≠ 0 := by
  exact (affineCoefficientEquiv k c B hB).isUnit_det'.ne_zero

theorem map_affineCoefficientMeasure (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) :
    Measure.map (affineCoefficientMap k c B) (coefficientMeasure k) =
      ENNReal.ofReal (|LinearMap.det (affineCoefficientMap k c B)|⁻¹) •
        coefficientMeasure k := by
  rw [coefficientMeasure_eq_volume]
  simpa only [abs_inv] using Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (affineCoefficientMap_det_ne_zero k c B hB)

theorem lintegral_affineCoefficientChange (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (f : CoefficientSpace k → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ F, f F ∂coefficientMeasure k) =
      ENNReal.ofReal (|LinearMap.det (affineCoefficientMap k c B)|⁻¹) *
        ∫⁻ J, f ((affineCoefficientEquiv k c B hB).symm J) ∂coefficientMeasure k := by
  let e := affineCoefficientEquiv k c B hB
  have he : Measurable e := e.toLinearMap.continuous_of_finiteDimensional.measurable
  have hi : Measurable e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional.measurable
  have h := lintegral_map (μ := coefficientMeasure k) (hf.comp hi) he
  have hm : Measure.map e (coefficientMeasure k) =
      ENNReal.ofReal (|LinearMap.det (affineCoefficientMap k c B)|⁻¹) •
        coefficientMeasure k := map_affineCoefficientMeasure k c B hB
  rw [hm, lintegral_smul_measure] at h
  simpa only [Function.comp_apply, e.symm_apply_apply, smul_eq_mul] using h.symm

/-- Conditional interface for the determinant character, retained explicitly.
AffineCharacterUses supplies it from the completed GeneralAffineCharacter proof. -/
theorem lintegral_affineCoefficientChange_of_character (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (hcharacter : |LinearMap.det (affineCoefficientMap k c B)| = |B.det| ^ chi k)
    (f : CoefficientSpace k → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ F, f F ∂coefficientMeasure k) =
      ENNReal.ofReal (|B.det| ^ (-(chi k : ℝ))) *
        ∫⁻ J, f ((affineCoefficientEquiv k c B hB).symm J) ∂coefficientMeasure k := by
  rw [lintegral_affineCoefficientChange k c B hB f hf, hcharacter]
  rw [Real.rpow_neg (abs_nonneg _) _, Real.rpow_natCast]

end PaperI
