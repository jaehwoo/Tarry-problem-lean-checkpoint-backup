import PaperILean.RotationChartPatchMeasure
import PaperILean.FiniteMeasureGluing

/-! I331: extend the proved local invariant coordinate measure by a fixed finite
chart cover. The cover, disjoint refinement and total mass have no e,t,F,R input. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix Matrix.L2OpNorm
namespace PaperI

def rotationChartInner : Set PhysicalSpace := {x | ‖skewMatrixOfCoordinates x‖ < 1/3}

theorem rotationChartInner_isOpen : IsOpen rotationChartInner :=
  isOpen_lt skewMatrixOfCoordinates_continuous.norm continuous_const

theorem rotationChartInner_subset_core : rotationChartInner ⊆ rotationChartCore := by
  intro x hx
  change ‖skewMatrixOfCoordinates x‖ ≤ 1/3
  exact (show ‖skewMatrixOfCoordinates x‖ < 1/3 from hx).le

theorem rotationChartInner_subset_source : rotationChartInner ⊆ rotationChartSource :=
  rotationChartInner_subset_core.trans rotationChartCore_subset_source

theorem zero_mem_rotationChartInner : (0 : PhysicalSpace) ∈ rotationChartInner := by
  simp only [rotationChartInner, mem_setOf_eq, skewMatrixOfCoordinates_zero, norm_zero]
  norm_num

theorem rotationChartInner_volume_positive : 0 < rotationChartVolume rotationChartInner :=
  rotationChartVolume_pos_of_physical_pos _ rotationChartInner_isOpen.measurableSet
    rotationChartInner_subset_core
    (rotationChartInner_isOpen.measure_pos physicalMeasure ⟨0, zero_mem_rotationChartInner⟩)

theorem rotationChartInner_volume_finite : rotationChartVolume rotationChartInner < ⊤ :=
  (measure_mono rotationChartInner_subset_core).trans_lt rotationChartVolume_core_lt_top

def rotationChartCorePatch (g : rotationGroup3) : Set rotationGroup3 :=
  (fun O => g * O) '' (rotationCoordinateExp '' rotationChartInner)

theorem rotationChartCorePatch_eq_image (g : rotationGroup3) :
    rotationChartCorePatch g = (fun x => g * rotationCoordinateExp x) '' rotationChartInner :=
  (image_comp _ _ _).symm

theorem rotationChartCorePatch_isOpen (g : rotationGroup3) : IsOpen (rotationChartCorePatch g) :=
  isOpenMap_mul_left g _
    (rotationExponentialChart.isOpen_image_of_subset_source rotationChartInner_isOpen
      rotationChartInner_subset_source)

theorem rotationChartCorePatch_subset (g : rotationGroup3) :
    rotationChartCorePatch g ⊆ rotationChartPatch g := by
  rw [rotationChartCorePatch_eq_image]
  exact rotationChartPatch_image_subset g _ rotationChartInner_subset_source

theorem self_mem_rotationChartCorePatch (g : rotationGroup3) : g ∈ rotationChartCorePatch g := by
  rw [rotationChartCorePatch_eq_image]
  refine ⟨0, zero_mem_rotationChartInner, ?_⟩
  change g * rotationCoordinateExp 0 = g
  rw [rotationCoordinateExp_zero, mul_one]

theorem rotationChartCorePatch_measure (g : rotationGroup3) :
    rotationChartPatchMeasure g (rotationChartCorePatch g) =
      rotationChartVolume rotationChartInner := by
  rw [rotationChartCorePatch_eq_image]
  exact rotationChartPatchMeasure_image g _ rotationChartInner_isOpen.measurableSet
    rotationChartInner_subset_source

theorem rotationChartCorePatch_finite_cover :
    ∃ n : ℕ, ∃ g : Fin n → rotationGroup3, ⋃ i, rotationChartCorePatch (g i) = univ := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover rotationChartCorePatch
    rotationChartCorePatch_isOpen (fun O _ => mem_iUnion.mpr ⟨O, self_mem_rotationChartCorePatch O⟩)
  refine ⟨s.card, fun i => (s.equivFin.symm i).val, eq_univ_of_forall ?_⟩
  intro O
  obtain ⟨g, hg, hO⟩ := mem_iUnion₂.mp (hs (mem_univ O))
  refine mem_iUnion.mpr ⟨s.equivFin ⟨g, hg⟩, ?_⟩
  simpa only [Equiv.symm_apply_apply] using hO

def rotationChartCoverSize : ℕ := rotationChartCorePatch_finite_cover.choose

def rotationChartCover : Fin rotationChartCoverSize → rotationGroup3 :=
  rotationChartCorePatch_finite_cover.choose_spec.choose

theorem rotationChartCover_covers :
    ⋃ i, rotationChartCorePatch (rotationChartCover i) = univ :=
  rotationChartCorePatch_finite_cover.choose_spec.choose_spec

def rotationInvariantVolume : Measure rotationGroup3 :=
  finiteChartGluedMeasure (fun i => rotationChartCorePatch (rotationChartCover i))
    (fun i => rotationChartPatchMeasure (rotationChartCover i))

theorem rotationInvariantVolume_restrict_patch (g : rotationGroup3) :
    rotationInvariantVolume.restrict (rotationChartPatch g) =
      (rotationChartPatchMeasure g).restrict (rotationChartPatch g) := by
  apply finiteChartGluedMeasure_agrees _ _
    (fun i => (rotationChartCorePatch_isOpen _).measurableSet) rotationChartCover_covers
    _ _ (rotationChartPatch_isOpen g).measurableSet
  intro i B hB hsub
  exact rotationChartPatchMeasure_compatible _ _ B hB
    (fun _ hx => rotationChartCorePatch_subset _ (hsub hx).2)
    (fun _ hx => (hsub hx).1)

theorem rotationInvariantVolume_apply_patch (g : rotationGroup3)
    (B : Set rotationGroup3) (hB : MeasurableSet B) (hsub : B ⊆ rotationChartPatch g) :
    rotationInvariantVolume B = rotationChartPatchMeasure g B := by
  have h := congrArg (fun μ : Measure rotationGroup3 => μ B)
    (rotationInvariantVolume_restrict_patch g)
  simpa only [Measure.restrict_apply hB, inter_eq_left.mpr hsub] using h

theorem rotationInvariantVolume_image (g : rotationGroup3)
    (A : Set PhysicalSpace) (hA : MeasurableSet A) (hsub : A ⊆ rotationChartSource) :
    rotationInvariantVolume ((fun x => g * rotationCoordinateExp x) '' A) =
      rotationChartVolume A := by
  have him : MeasurableSet ((fun x => g * rotationCoordinateExp x) '' A) := by
    rw [show (fun x => g * rotationCoordinateExp x) = (fun O => g * O) ∘
      rotationCoordinateExp from rfl, image_comp]
    exact (MeasurableEquiv.mulLeft g).measurableSet_image.mpr
      (rotationCoordinateExp_image_measurableSet A hA hsub)
  rw [rotationInvariantVolume_apply_patch g _ him (rotationChartPatch_image_subset g A hsub)]
  exact rotationChartPatchMeasure_image g A hA hsub

theorem rotationInvariantVolume_univ_finite : rotationInvariantVolume univ < ⊤ := by
  apply finiteChartGluedMeasure_finite
  intro i
  rw [rotationChartCorePatch_measure]
  exact rotationChartInner_volume_finite

theorem rotationInvariantVolume_isFiniteMeasure : IsFiniteMeasure rotationInvariantVolume :=
  ⟨rotationInvariantVolume_univ_finite⟩

attribute [instance] rotationInvariantVolume_isFiniteMeasure

theorem rotationInvariantVolume_univ_positive : 0 < rotationInvariantVolume univ := by
  have h := rotationInvariantVolume_image 1 rotationChartInner
    rotationChartInner_isOpen.measurableSet rotationChartInner_subset_source
  exact (rotationChartInner_volume_positive.trans_eq h.symm).trans_le (measure_mono (subset_univ _))

theorem rotationInvariantVolume_preimage_patch (g h : rotationGroup3)
    (B : Set rotationGroup3) (hB : MeasurableSet B) (hsub : B ⊆ rotationChartPatch h) :
    rotationInvariantVolume ((fun O => g * O) ⁻¹' B) = rotationInvariantVolume B := by
  have hpre : (fun O => g * O) ⁻¹' B ⊆ rotationChartPatch (g⁻¹ * h) := by
    intro O hO
    have := hsub hO
    simpa only [rotationChartPatch, mem_preimage, mul_inv_rev, inv_inv, mul_assoc] using this
  rw [rotationInvariantVolume_apply_patch (g⁻¹ * h) _
    (hB.preimage (measurable_const_mul g)) hpre,
    rotationChartPatchMeasure_preimage g _ B hB, mul_inv_cancel_left,
    rotationInvariantVolume_apply_patch h B hB hsub]

theorem rotationInvariantVolume_isMulLeftInvariant :
    Measure.IsMulLeftInvariant rotationInvariantVolume := by
  constructor
  intro g
  apply Measure.ext_of_iUnion_eq_univ rotationChartCover_covers
  intro i
  apply Measure.ext
  intro B hB
  have hi := (rotationChartCorePatch_isOpen (rotationChartCover i)).measurableSet
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
    Measure.map_apply (measurable_const_mul g) (hB.inter hi)]
  exact rotationInvariantVolume_preimage_patch g (rotationChartCover i) _ (hB.inter hi)
    (inter_subset_right.trans (rotationChartCorePatch_subset _))

attribute [instance] rotationInvariantVolume_isMulLeftInvariant

end PaperI
