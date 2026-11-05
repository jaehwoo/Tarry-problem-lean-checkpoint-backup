import PaperILean.FiniteMultiplicityVolume
import PaperILean.RegularCoefficientFiberBounds

/-! I660/I662/I665: actual selected preimages satisfy the measure estimate.
The multiplicity bound is chosen before all external parameters, output sets,
and positive determinant thresholds. Only the selected domain must be
measurable; pointwise differentiability supplies its relative continuity. -/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure FirstOrder
open scoped ENNReal
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- Restricting the selected domain cannot increase a genuinely finite fiber. -/
theorem finite_fiber_bound_mono {α β : Type*} (f : α → β) {s t : Set α}
    (hst : s ⊆ t) (N : ℕ)
    (hN : ∀ y, Finite {x : α | x ∈ t ∧ f x = y} ∧
      Nat.card {x : α | x ∈ t ∧ f x = y} ≤ N) :
    ∀ y, Finite {x : α | x ∈ s ∧ f x = y} ∧
      Nat.card {x : α | x ∈ s ∧ f x = y} ≤ N := by
  intro y
  letI := (hN y).1
  let g : {x : α | x ∈ s ∧ f x = y} → {x : α | x ∈ t ∧ f x = y} :=
    fun x => ⟨x.val, hst x.property.1, x.property.2⟩
  have hg : Function.Injective g := fun _ _ h => Subtype.ext (congrArg Subtype.val h)
  exact ⟨Finite.of_injective g hg, (Nat.card_le_card_of_injective g hg).trans (hN y).2⟩

/-- The preimage estimate for a measurable selected regular domain. -/
theorem regular_preimage_measure_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (Ω Q : Set E) (hΩ : MeasurableSet Ω) (hQ : MeasurableSet Q)
    (f' : E → E →L[ℝ] E) (hf' : ∀ x ∈ Ω, HasFDerivAt f (f' x) x)
    (δ : ℝ) (hδ : 0 < δ) (hdet : ∀ x ∈ Ω, δ ≤ |(f' x).det|)
    (N : ℕ) (hN : ∀ y, Finite {x : E | x ∈ Ω ∧ f x = y} ∧
      Nat.card {x : E | x ∈ Ω ∧ f x = y} ≤ N) :
    μ (Ω ∩ f ⁻¹' Q) ≤ ((N : ℝ≥0∞) / ENNReal.ofReal δ) * μ Q := by
  classical
  have hc : ContinuousOn f Ω := fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hm := hc.measurable_piecewise continuous_zero.continuousOn hΩ
  have hs : MeasurableSet (Ω ∩ f ⁻¹' Q) := by
    convert hΩ.inter (hm hQ) using 1
    ext x
    by_cases hx : x ∈ Ω <;> simp [hx]
  exact finite_multiplicity_measure_le μ f (Ω ∩ f ⁻¹' Q) Q hs hQ
    (fun _ hx => hx.2) f' (fun x hx => hf' x hx.1) δ hδ
    (fun x hx => hdet x hx.1) N (finite_fiber_bound_mono f inter_subset_left N hN)

/-- One fixed joint selected graph supplies N before external parameter,
Jacobian threshold and output set. This is the manuscript's fixed-slice
area estimate, relative to the already named real-algebraic inputs. -/
theorem published_regularCoefficient_preimage_volume_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (Ω : (ι → ℝ) → Set (κ → ℝ)) (T : (ι → ℝ) → (κ → ℝ) → (κ → ℝ))
    (hGraph : (Set.univ : Set ℝ).Definable Language.ring (regularCoefficientGraph Ω T)) :
    ∃ N : ℕ, ∀ (p : ι → ℝ) (δ : ℝ), 0 < δ → MeasurableSet (Ω p) →
      (∀ x ∈ Ω p, ∃ L : (κ → ℝ) →L[ℝ] (κ → ℝ),
        HasFDerivAt (T p) L x ∧ δ ≤ |L.det|) →
      ∀ Q : Set (κ → ℝ), MeasurableSet Q →
        volume (Ω p ∩ (T p) ⁻¹' Q) ≤
          ((N : ℝ≥0∞) / ENNReal.ofReal δ) * volume Q := by
  obtain ⟨N, hN⟩ := published_regularCoefficientFiber_bound_of_jacobian_lower_bound
    hCells hHardt hQQE Ω T hGraph
  refine ⟨N, ?_⟩
  intro p δ hδ hΩ hreg Q hQ
  have hf (x) (hx : x ∈ Ω p) : HasFDerivAt (T p) (fderiv ℝ (T p) x) x :=
    (hreg x hx).choose_spec.1.differentiableAt.hasFDerivAt
  have hd (x) (hx : x ∈ Ω p) : δ ≤ |(fderiv ℝ (T p) x).det| := by
    obtain ⟨L, hL, hd⟩ := hreg x hx
    simpa only [hL.fderiv] using hd
  exact regular_preimage_measure_le volume (T p) (Ω p) Q hΩ hQ
    (fderiv ℝ (T p)) hf δ hδ hd N (fun y => hN p y δ hδ hreg)

end PaperI
