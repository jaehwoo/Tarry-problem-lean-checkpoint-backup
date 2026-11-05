import PaperILean.RegularCoefficientInjectivePartition
import PaperILean.FiniteMultiplicityMeasure

/-! The finite-multiplicity measure estimate used in I665, derived from
mathlib's checked injective change-of-variables theorem by measurable
partition and finite-overlap counting. No new external area axiom or
Lipschitz premise is needed. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace PaperI

/-- The determinant lower bound controls the measure of an injective piece. -/
theorem measure_le_inverse_jacobian_mul_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (s : Set E) (hs : MeasurableSet s)
    (f' : E → E →L[ℝ] E) (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hinj : InjOn f s) (δ : ℝ) (hδ : 0 < δ)
    (hdet : ∀ x ∈ s, δ ≤ |(f' x).det|) :
    μ s ≤ (ENNReal.ofReal δ)⁻¹ * μ (f '' s) := by
  apply (ENNReal.mul_le_iff_le_inv (ENNReal.ofReal_pos.mpr hδ).ne'
    ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal δ * μ s = ∫⁻ _ in s, ENNReal.ofReal δ ∂μ :=
      (setLIntegral_const s _).symm
    _ ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ :=
      setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (hdet x hx))
    _ = μ (f '' s) := lintegral_abs_det_fderiv_eq_addHaar_image μ hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hinj

/-- A finite uniform number of preimages and a positive actual Jacobian
lower bound imply the required measure estimate on any measurable source.
Both zero multiplicity and infinite output measure are allowed. -/
theorem finite_multiplicity_measure_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (s Q : Set E) (hs : MeasurableSet s) (hQ : MeasurableSet Q)
    (hto : MapsTo f s Q) (f' : E → E →L[ℝ] E)
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (δ : ℝ) (hδ : 0 < δ) (hdet : ∀ x ∈ s, δ ≤ |(f' x).det|)
    (N : ℕ) (hN : ∀ y, Finite {x : E | x ∈ s ∧ f x = y} ∧
      Nat.card {x : E | x ∈ s ∧ f x = y} ≤ N) :
    μ s ≤ ((N : ℝ≥0∞) / ENNReal.ofReal δ) * μ Q := by
  obtain ⟨t, ht, hd, hcover, hinj⟩ :=
    exists_measurable_injective_partition_of_det_ne_zero f s hs f' hf'
      (fun x hx => abs_pos.mp (hδ.trans_le (hdet x hx)))
  have hsub (i) : t i ⊆ s := by rw [← hcover]; exact subset_iUnion t i
  have him (i) : MeasurableSet (f '' t i) := measurable_image_of_fderivWithin (ht i)
    (fun x hx => (hf' x (hsub i hx)).hasFDerivWithinAt) (hinj i)
  have hb (i) : μ (t i) ≤ (ENNReal.ofReal δ)⁻¹ * μ (f '' t i) :=
    measure_le_inverse_jacobian_mul_image μ f (t i) (ht i) f'
      (fun x hx => hf' x (hsub i hx)) (hinj i) δ hδ (fun x hx => hdet x (hsub i hx))
  calc
    μ s = ∑' i, μ (t i) := by rw [← hcover, measure_iUnion hd ht]
    _ ≤ ∑' i, (ENNReal.ofReal δ)⁻¹ * μ (f '' t i) := ENNReal.tsum_le_tsum hb
    _ = (ENNReal.ofReal δ)⁻¹ * ∑' i, μ (f '' t i) := ENNReal.tsum_mul_left
    _ ≤ (ENNReal.ofReal δ)⁻¹ * ((N : ℝ≥0∞) * μ Q) := by
      gcongr
      exact tsum_image_measure_le_of_fiber_bound μ f s t Q hQ hsub hd him
        (fun i => image_subset_iff.mpr (fun _ hx => hto (hsub i hx))) N hN
    _ = ((N : ℝ≥0∞) / ENNReal.ofReal δ) * μ Q := by
      simp only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

end PaperI
