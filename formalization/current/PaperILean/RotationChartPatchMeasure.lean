import PaperILean.RotationChartVolume
import PaperILean.RotationHaarMeasure

/-! I331: compatible measures on actual left-translated chart patches.
These are not yet a global invariant measure. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix Matrix.L2OpNorm
namespace PaperI

def rotationChartPatch (g : rotationGroup3) : Set rotationGroup3 :=
  (fun O => g⁻¹ * O) ⁻¹' rotationChartTarget

def rotationChartPatchCoordinates (g : rotationGroup3) (B : Set rotationGroup3) :
    Set PhysicalSpace :=
  (fun x => g * rotationCoordinateExp x) ⁻¹' B ∩ rotationChartSource

def rotationChartPatchMeasure (g : rotationGroup3) : Measure rotationGroup3 :=
  Measure.map (fun x => g * rotationCoordinateExp x)
    (rotationChartVolume.restrict rotationChartSource)

theorem rotationChartPatch_isOpen (g : rotationGroup3) : IsOpen (rotationChartPatch g) :=
  rotationChartTarget_isOpen.preimage (continuous_const.mul continuous_id)

theorem rotationChartPatchCoordinates_measurable (g : rotationGroup3)
    (B : Set rotationGroup3) (hB : MeasurableSet B) :
    MeasurableSet (rotationChartPatchCoordinates g B) :=
  (hB.preimage (measurable_const.mul rotationCoordinateExp_measurable)).inter
    rotationChartSource_isOpen.measurableSet

theorem rotationChartPatchMeasure_apply (g : rotationGroup3)
    (B : Set rotationGroup3) (hB : MeasurableSet B) :
    rotationChartPatchMeasure g B = rotationChartVolume (rotationChartPatchCoordinates g B) := by
  rw [rotationChartPatchMeasure, Measure.map_apply
    (measurable_const.mul rotationCoordinateExp_measurable) hB,
    Measure.restrict_apply (hB.preimage (measurable_const.mul rotationCoordinateExp_measurable))]
  rfl

theorem rotationChartPatchCoordinates_overlap (g h : rotationGroup3)
    (B : Set rotationGroup3) (hsub : B ⊆ rotationChartPatch h) :
    rotationChartPatchCoordinates g B ⊆ rotationChartTranslationSource (h⁻¹ * g) := by
  intro x hx
  refine ⟨hx.2, ?_⟩
  simpa only [rotationChartPatch, mem_preimage, mul_assoc] using hsub hx.1

theorem rotationChartPatchCoordinates_transition (g h : rotationGroup3)
    (B : Set rotationGroup3) (hg : B ⊆ rotationChartPatch g)
    (hh : B ⊆ rotationChartPatch h) :
    rotationChartLeftTranslation (h⁻¹ * g) '' rotationChartPatchCoordinates g B =
      rotationChartPatchCoordinates h B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have ho := rotationChartPatchCoordinates_overlap g h B hh hx
    refine ⟨?_, rotationChartLeftTranslation_mem_source _ _ ho⟩
    change h * rotationCoordinateExp (rotationChartLeftTranslation (h⁻¹ * g) x) ∈ B
    rw [rotationChartLeftTranslation_exp _ _ ho]
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hx.1
  · intro hy
    have ho := rotationChartPatchCoordinates_overlap h g B hg hy
    let x := rotationChartLeftTranslation (g⁻¹ * h) y
    have hxexp : rotationCoordinateExp x = (g⁻¹ * h) * rotationCoordinateExp y :=
      rotationChartLeftTranslation_exp _ _ ho
    refine ⟨x, ⟨?_, rotationChartLeftTranslation_mem_source _ _ ho⟩, ?_⟩
    · change g * rotationCoordinateExp x ∈ B
      rw [hxexp]
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hy.1
    · change rotationCoordinateLog ((h⁻¹ * g) * rotationCoordinateExp x) = y
      rw [hxexp]
      simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left] using
        rotationCoordinateLog_coordinateExp y hy.2

theorem rotationChartPatchMeasure_compatible (g h : rotationGroup3)
    (B : Set rotationGroup3) (hB : MeasurableSet B)
    (hg : B ⊆ rotationChartPatch g) (hh : B ⊆ rotationChartPatch h) :
    rotationChartPatchMeasure g B = rotationChartPatchMeasure h B := by
  rw [rotationChartPatchMeasure_apply g B hB, rotationChartPatchMeasure_apply h B hB]
  rw [← rotationChartPatchCoordinates_transition g h B hg hh]
  exact (rotationChartVolume_translation (h⁻¹ * g) _
    (rotationChartPatchCoordinates_measurable g B hB)
    (rotationChartPatchCoordinates_overlap g h B hh)).symm

theorem rotationChartPatchMeasure_left_translate (g h : rotationGroup3)
    (B : Set rotationGroup3) (hB : MeasurableSet B) :
    rotationChartPatchMeasure (g * h) ((fun O => g * O) '' B) =
      rotationChartPatchMeasure h B := by
  have him : MeasurableSet ((fun O => g * O) '' B) :=
    (MeasurableEquiv.mulLeft g).measurableSet_image.mpr hB
  rw [rotationChartPatchMeasure_apply _ _ him, rotationChartPatchMeasure_apply _ _ hB]
  congr 1
  ext x
  simp only [rotationChartPatchCoordinates, mem_inter_iff, mem_preimage, mem_image,
    mul_assoc, mul_right_inj, exists_eq_right]

theorem rotationChartPatchMeasure_image (g : rotationGroup3)
    (A : Set PhysicalSpace) (hA : MeasurableSet A) (hsub : A ⊆ rotationChartSource) :
    rotationChartPatchMeasure g ((fun x => g * rotationCoordinateExp x) '' A) =
      rotationChartVolume A := by
  have him : MeasurableSet ((fun x => g * rotationCoordinateExp x) '' A) := by
    rw [show (fun x => g * rotationCoordinateExp x) = (fun O => g * O) ∘
      rotationCoordinateExp from rfl, image_comp]
    exact (MeasurableEquiv.mulLeft g).measurableSet_image.mpr
      (rotationCoordinateExp_image_measurableSet A hA hsub)
  rw [rotationChartPatchMeasure_apply _ _ him]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨y, hy, heq⟩, hx⟩
    have : y = x := rotationCoordinateExp_injOn_chart (hsub hy) hx (mul_left_cancel heq)
    simpa only [this] using hy
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, hsub hx⟩

theorem rotationChartPatchMeasure_preimage (g h : rotationGroup3)
    (B : Set rotationGroup3) (hB : MeasurableSet B) :
    rotationChartPatchMeasure h ((fun O => g * O) ⁻¹' B) =
      rotationChartPatchMeasure (g * h) B := by
  rw [rotationChartPatchMeasure_apply _ _ (hB.preimage (measurable_const_mul g)),
    rotationChartPatchMeasure_apply _ _ hB]
  congr 1
  ext x
  simp only [rotationChartPatchCoordinates, mem_inter_iff, mem_preimage, mul_assoc]

theorem rotationChartPatch_image_subset (g : rotationGroup3)
    (A : Set PhysicalSpace) (hsub : A ⊆ rotationChartSource) :
    (fun x => g * rotationCoordinateExp x) '' A ⊆ rotationChartPatch g := by
  rintro O ⟨x, hx, rfl⟩
  change g⁻¹ * (g * rotationCoordinateExp x) ∈ rotationChartTarget
  simpa only [inv_mul_cancel_left] using rotationCoordinateExp_mapsTo_chart (hsub hx)

end PaperI
