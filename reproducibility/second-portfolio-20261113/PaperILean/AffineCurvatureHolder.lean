import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! I3325[600,624) + I3326-I3330: the complete Hölder estimate for
absolute affine-curvature area, from the preceding geometric integral bounds. -/
open MeasureTheory
open scoped ENNReal

namespace PaperI.AffineCurvatureHolder

/-- The actual signed curvature and area measure satisfy the displayed Hölder
estimate and its uniform physical-radius bound. Integrability is derived. -/
theorem affine_curvature_holder_stage
    (Ccurv Carea : ℝ) (hCcurv : 0 ≤ Ccurv) (hCarea : 0 ≤ Carea)
    (R : ℝ) (hR : 0 ≤ R) (α : Type) [MeasurableSpace α]
    (μ : Measure α) (K : α → ℝ) (hK : AEMeasurable K μ)
    (hcurv : (∫⁻ x, ENNReal.ofReal |K x| ∂μ) ≤ ENNReal.ofReal Ccurv)
    (harea : μ Set.univ ≤ ENNReal.ofReal (Carea * R ^ 2)) :
    Integrable (fun x => |K x|) μ ∧
    Integrable (fun x => |K x| ^ (1 / 4 : ℝ)) μ ∧
    (∫ x, |K x| ^ (1 / 4 : ℝ) ∂μ) ≤
      (∫ x, |K x| ∂μ) ^ (1 / 4 : ℝ) * (μ Set.univ).toReal ^ (3 / 4 : ℝ) ∧
    (∫ x, |K x| ^ (1 / 4 : ℝ) ∂μ) ≤
      Ccurv ^ (1 / 4 : ℝ) * Carea ^ (3 / 4 : ℝ) * R ^ (3 / 2 : ℝ) := by
  have hk : AEMeasurable (fun x => ENNReal.ofReal |K x|) μ := by
    simpa only [Real.norm_eq_abs] using hK.norm.ennreal_ofReal
  have hcfin : (∫⁻ x, ENNReal.ofReal |K x| ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcurv
  have hafin : μ Set.univ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top harea
  have hh : (∫⁻ x, ENNReal.ofReal |K x| ^ (1 / 4 : ℝ) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal |K x| ∂μ) ^ (1 / 4 : ℝ) *
        μ Set.univ ^ (3 / 4 : ℝ) := by
    simpa only [ENNReal.one_rpow, mul_one, lintegral_one] using
      (ENNReal.lintegral_mul_norm_pow_le hk
        (g := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
        (p := (1 / 4 : ℝ)) (q := (3 / 4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num))
  have hbfin : (∫⁻ x, ENNReal.ofReal |K x| ∂μ) ^ (1 / 4 : ℝ) *
      μ Set.univ ^ (3 / 4 : ℝ) ≠ ⊤ :=
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hcfin)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hafin)).ne
  have hqfin : (∫⁻ x, ENNReal.ofReal |K x| ^ (1 / 4 : ℝ) ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top hbfin hh
  have hi : Integrable (fun x => |K x|) μ := by
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using
      integrable_toReal_of_lintegral_ne_top hk hcfin
  have hqi : Integrable (fun x => |K x| ^ (1 / 4 : ℝ)) μ := by
    simpa only [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _)] using
      integrable_toReal_of_lintegral_ne_top (hk.pow_const (1 / 4 : ℝ)) hqfin
  have hci : (∫ x, |K x| ∂μ) = (∫⁻ x, ENNReal.ofReal |K x| ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => abs_nonneg (K x))
      hi.aestronglyMeasurable
  have hq : (∫ x, |K x| ^ (1 / 4 : ℝ) ∂μ) =
      (∫⁻ x, ENNReal.ofReal |K x| ^ (1 / 4 : ℝ) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg (K x)) _)
      hqi.aestronglyMeasurable]
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hreal : (∫ x, |K x| ^ (1 / 4 : ℝ) ∂μ) ≤
      (∫ x, |K x| ∂μ) ^ (1 / 4 : ℝ) * (μ Set.univ).toReal ^ (3 / 4 : ℝ) := by
    rw [hq, hci]
    simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using
      ENNReal.toReal_mono hbfin hh
  have hc : (∫ x, |K x| ∂μ) ≤ Ccurv := by
    rw [hci]
    simpa only [ENNReal.toReal_ofReal hCcurv] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hcurv
  have ha : (μ Set.univ).toReal ≤ Carea * R ^ 2 := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hCarea (sq_nonneg R))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top harea
  refine ⟨hi, hqi, hreal, hreal.trans ?_⟩
  calc
    (∫ x, |K x| ∂μ) ^ (1 / 4 : ℝ) * (μ Set.univ).toReal ^ (3 / 4 : ℝ) ≤
        Ccurv ^ (1 / 4 : ℝ) * (Carea * R ^ 2) ^ (3 / 4 : ℝ) :=
      mul_le_mul (Real.rpow_le_rpow (integral_nonneg fun x => abs_nonneg (K x)) hc (by norm_num))
        (Real.rpow_le_rpow ENNReal.toReal_nonneg ha (by norm_num))
        (Real.rpow_nonneg ENNReal.toReal_nonneg _) (Real.rpow_nonneg hCcurv _)
    _ = Ccurv ^ (1 / 4 : ℝ) * Carea ^ (3 / 4 : ℝ) * R ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow hCarea (sq_nonneg R), ← Real.rpow_natCast R 2,
        ← Real.rpow_mul hR]
      norm_num
      ring

end PaperI.AffineCurvatureHolder
