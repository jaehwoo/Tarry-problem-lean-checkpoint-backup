import PaperILean.I2385ProductHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! The inverse-action passage needed in the conditional H0 integral at I3350.
This uses the saved coordinate Haar normalization and measure-preserving shear;
no Haar bound or subgroup-pivot conclusion is assumed here. -/
noncomputable section
namespace PaperI.PhysicalH0Inverse

open MeasureTheory I2385ProductHaar

/-- The literal inverse of the original six-coordinate affine frame is measurable. -/
theorem measurable_inv : Measurable originalUpperAffineInv := by
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i <;> simp [originalUpperAffineInv] <;> fun_prop

/-- Actual affine inversion reverses composition, including every translation term. -/
theorem inv_comp (g h : Upper) :
    originalUpperAffineInv (originalUpperAffineComp g h) =
      originalUpperAffineComp (originalUpperAffineInv h) (originalUpperAffineInv g) := by
  ext i
  fin_cases i <;> simp [originalUpperAffineInv, originalUpperAffineComp] <;> ring

/-- In coordinates (d,a,b,c0), H0 inversion is the saved shear after reflection. -/
theorem actual_inv_coordinates (p : Quad) :
    originalUpperAffineInv (h0Coordinates p) =
      h0Coordinates (productShear (-p)) := by
  ext i
  fin_cases i <;> simp [originalUpperAffineInv, h0Coordinates, productShear, fiberShear] <;>
    ring

private theorem measurePreserving_coordinateInverse :
    MeasurePreserving (fun p : Quad => productShear (-p)) volume volume := by
  have hneg : MeasurePreserving (fun p : Quad => -p) volume volume := by
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      ((Measure.measurePreserving_neg (volume : Measure ℝ)).prod
        ((Measure.measurePreserving_neg (volume : Measure ℝ)).prod
          (Measure.measurePreserving_neg (volume : Measure ℝ))))
  simpa only [Function.comp_def] using measurePreserving_productShear.comp hneg

/-- Inversion preserves the manuscript's actual coordinate Haar measure on H0. -/
theorem map_inv_haar0 : Measure.map originalUpperAffineInv haar0 = haar0 := by
  unfold haar0
  rw [Measure.map_map measurable_inv continuous_h0Coordinates.measurable]
  have heq : originalUpperAffineInv ∘ h0Coordinates =
      h0Coordinates ∘ (fun p : Quad => productShear (-p)) := by
    funext p
    exact actual_inv_coordinates p
  rw [heq, ← Measure.map_map continuous_h0Coordinates.measurable
    measurePreserving_coordinateInverse.measurable,
    measurePreserving_coordinateInverse.map_eq]

end PaperI.PhysicalH0Inverse
