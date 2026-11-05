import Mathlib.MeasureTheory.Measure.Prod

/-! The final Fubini step in I657--667. The parameter remains in the product
measure. Joint measurability, rather than sectionwise measurability alone, is
retained. Bounds use ENNReal, so empty domains and infinite output/parameter
measure require no hidden finiteness or cancellation assumptions.

Pre-strategy tests: evidence/checkpoint_107_fubini_pre_strategy.{py,json}.
These results integrate an independently supplied slice estimate; they do not
assert an area formula or establish the manuscript's selected branch data. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PaperI

/-- A measurable joint set is bounded by any pointwise bound on its slices,
with the external parameter measure restricted to the stated region. -/
theorem joint_measure_le_integral_slice_bound
    {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]
    (μ : Measure P) (ν : Measure X) [SFinite ν]
    (Z : Set P) (hZ : MeasurableSet Z) (A : Set (P × X))
    (hA : MeasurableSet A) (b : P → ℝ≥0∞)
    (hb : ∀ p ∈ Z, ν {x | (p, x) ∈ A} ≤ b p) :
    ((μ.restrict Z).prod ν) A ≤ ∫⁻ p in Z, b p ∂μ := by
  rw [Measure.prod_apply hA]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hZ] with p hp
  exact hb p hp

/-- Uniformity is explicit: one constant C and one output measure V precede
all parameters. No real-valued conversion of possibly infinite measures occurs. -/
theorem joint_measure_le_uniform_slice_bound
    {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]
    (μ : Measure P) (ν : Measure X) [SFinite ν]
    (Z : Set P) (hZ : MeasurableSet Z) (A : Set (P × X))
    (hA : MeasurableSet A) (C V : ℝ≥0∞)
    (hbound : ∀ p ∈ Z, ν {x | (p, x) ∈ A} ≤ C * V) :
    ((μ.restrict Z).prod ν) A ≤ C * μ Z * V := by
  have h := joint_measure_le_integral_slice_bound μ ν Z hZ A hA
    (fun _ => C * V) hbound
  simpa only [setLIntegral_const, mul_assoc, mul_comm V (μ Z)] using h

/-- The explicit joint region equals restricting only the parameter measure. -/
theorem joint_region_measure_eq_restrict_prod
    {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]
    (μ : Measure P) (ν : Measure X) [SFinite ν]
    (Z : Set P) (A : Set (P × X)) (hA : MeasurableSet A) :
    (μ.prod ν) (A ∩ (Z ×ˢ Set.univ)) = ((μ.restrict Z).prod ν) A := by
  rw [← Measure.restrict_apply hA, ← Measure.prod_restrict]
  simp

/-- Measurability of the actual joint preimage is proved from the joint
selected domain and joint map. Measurable sections alone are not substituted. -/
theorem measurableSet_joint_preimage
    {P X Y : Type*} [MeasurableSpace P] [MeasurableSpace X] [MeasurableSpace Y]
    (Ω : Set (P × X)) (hΩ : MeasurableSet Ω) (T : P × X → Y)
    (hT : Measurable T) (Q : Set Y) (hQ : MeasurableSet Q) :
    MeasurableSet (Ω ∩ T ⁻¹' Q) := hΩ.inter (hT hQ)

/-- The Fubini conclusion for a jointly measurable selected coefficient map.
The slice estimate is an explicit local prerequisite, not an axiom; the
area-formula module supplies it after its own regularity and multiplicity checks. -/
theorem joint_preimage_measure_le_uniform_slice_bound
    {P X Y : Type*} [MeasurableSpace P] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure P) (ν : Measure X) (λ : Measure Y) [SFinite ν]
    (Z : Set P) (hZ : MeasurableSet Z)
    (Ω : Set (P × X)) (hΩ : MeasurableSet Ω)
    (T : P × X → Y) (hT : Measurable T)
    (Q : Set Y) (hQ : MeasurableSet Q) (C : ℝ≥0∞)
    (hbound : ∀ p ∈ Z,
      ν {x | (p, x) ∈ Ω ∧ T (p, x) ∈ Q} ≤ C * λ Q) :
    (μ.prod ν) ((Ω ∩ T ⁻¹' Q) ∩ (Z ×ˢ Set.univ)) ≤ C * μ Z * λ Q := by
  have hA := measurableSet_joint_preimage Ω hΩ T hT Q hQ
  rw [joint_region_measure_eq_restrict_prod μ ν Z _ hA]
  exact joint_measure_le_uniform_slice_bound μ ν Z hZ _ hA C (λ Q) hbound

end PaperI
