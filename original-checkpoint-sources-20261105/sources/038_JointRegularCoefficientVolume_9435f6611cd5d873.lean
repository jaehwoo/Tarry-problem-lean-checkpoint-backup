import PaperILean.RegularCoefficientVolume
import PaperILean.SelectedGraphMeasurability

/-! I666: the external parameters remain in the joint measure and are
integrated by Fubini. The finite-multiplicity slice estimate is proved in
RegularCoefficientVolume, not postulated here. Exact joint graph definability
supplies Borel measurability even when no measurable extension off the selected
domain was given. The bound N precedes parameter regions, thresholds and Q.
Pre-strategy: checkpoint_107_fubini_pre_strategy.{py,json}. -/

noncomputable section
open Set MeasureTheory FirstOrder
open scoped ENNReal
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- Nonuniform positive thresholds stay inside the parameter integral.
They cannot silently be replaced by one common positive threshold. -/
theorem published_joint_coefficient_volume_le_integral
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (Ω : (ι → ℝ) → Set (κ → ℝ))
    (T : (ι → ℝ) → (κ → ℝ) → (κ → ℝ))
    (hGraph : (Set.univ : Set ℝ).Definable Language.ring (regularCoefficientGraph Ω T)) :
    ∃ N : ℕ, ∀ (Z : Set (ι → ℝ)), MeasurableSet Z →
      ∀ (δ : (ι → ℝ) → ℝ), (∀ p ∈ Z, 0 < δ p) →
      (∀ p ∈ Z, ∀ x ∈ Ω p, ∃ L : (κ → ℝ) →L[ℝ] (κ → ℝ),
        HasFDerivAt (T p) L x ∧ δ p ≤ |L.det|) →
      ∀ Q : Set (κ → ℝ), MeasurableSet Q →
        volume {z : (ι → ℝ) × (κ → ℝ) |
          z.1 ∈ Z ∧ z.2 ∈ Ω z.1 ∧ T z.1 z.2 ∈ Q} ≤
            ∫⁻ p in Z, ((N : ℝ≥0∞) / ENNReal.ofReal (δ p)) * volume Q := by
  obtain ⟨N, hN⟩ := published_definable_regularCoefficient_volume_bound
    hCells hHardt hQQE Ω T hGraph
  refine ⟨N, ?_⟩
  intro Z hZ δ hδ hreg Q hQ
  let A : Set ((ι → ℝ) × (κ → ℝ)) :=
    {z | z.2 ∈ Ω z.1 ∧ T z.1 z.2 ∈ Q}
  have hA : MeasurableSet A := published_measurableSet_joint_coefficient_preimage
    hQQE.toRealSemialgebraicity hHardt Ω T hGraph Q hQ
  have hb : ∀ p ∈ Z, volume {x | (p, x) ∈ A} ≤
      ((N : ℝ≥0∞) / ENNReal.ofReal (δ p)) * volume Q := by
    intro p hp
    exact hN p (δ p) (hδ p hp) (hreg p hp) Q hQ
  have h := joint_measure_le_integral_slice_bound volume volume Z hZ A hA
    (fun p => ((N : ℝ≥0∞) / ENNReal.ofReal (δ p)) * volume Q) hb
  rw [← joint_region_measure_eq_restrict_prod volume volume Z A hA] at h
  convert h using 1
  ext z
  simp [A, and_comm, and_left_comm]

/-- Uniform coefficient-map volume bound after joint parameter integration.
One N is fixed before Z, delta and Q. No finite-volume hypothesis is needed. -/
theorem published_joint_coefficient_volume_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (Ω : (ι → ℝ) → Set (κ → ℝ))
    (T : (ι → ℝ) → (κ → ℝ) → (κ → ℝ))
    (hGraph : (Set.univ : Set ℝ).Definable Language.ring (regularCoefficientGraph Ω T)) :
    ∃ N : ℕ, ∀ (Z : Set (ι → ℝ)), MeasurableSet Z →
      ∀ (δ : ℝ), 0 < δ →
      (∀ p ∈ Z, ∀ x ∈ Ω p, ∃ L : (κ → ℝ) →L[ℝ] (κ → ℝ),
        HasFDerivAt (T p) L x ∧ δ ≤ |L.det|) →
      ∀ Q : Set (κ → ℝ), MeasurableSet Q →
        volume {z : (ι → ℝ) × (κ → ℝ) |
          z.1 ∈ Z ∧ z.2 ∈ Ω z.1 ∧ T z.1 z.2 ∈ Q} ≤
            ((N : ℝ≥0∞) / ENNReal.ofReal δ) * volume Z * volume Q := by
  obtain ⟨N, hN⟩ := published_joint_coefficient_volume_le_integral
    hCells hHardt hQQE Ω T hGraph
  refine ⟨N, ?_⟩
  intro Z hZ δ hδ hreg Q hQ
  have h := hN Z hZ (fun _ => δ) (fun _ _ => hδ) hreg Q hQ
  simpa only [setLIntegral_const, mul_assoc, mul_comm (volume Q) (volume Z)] using h

/-- Concrete polynomial coefficient maps satisfy the joint-volume estimate.
The joint graph and differentiability are proved from q, and only its actual
Jacobian lower bound remains to be checked in a manuscript application. -/
theorem published_joint_regularPolynomial_volume_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (q : κ → MvPolynomial (ι ⊕ κ) ℝ) (U : Set ((ι ⊕ κ) → ℝ))
    (hU : (Set.univ : Set ℝ).Definable Language.ring U) :
    ∃ N : ℕ, ∀ (Z : Set (ι → ℝ)), MeasurableSet Z →
      ∀ (δ : ℝ), 0 < δ →
      (∀ p ∈ Z, ∀ x, Sum.elim p x ∈ U →
        δ ≤ |(fderiv ℝ (regularPolynomialMap q p) x).det|) →
      ∀ Q : Set (κ → ℝ), MeasurableSet Q →
        volume {z : (ι → ℝ) × (κ → ℝ) |
          z.1 ∈ Z ∧ Sum.elim z.1 z.2 ∈ U ∧ regularPolynomialMap q z.1 z.2 ∈ Q} ≤
            ((N : ℝ≥0∞) / ENNReal.ofReal δ) * volume Z * volume Q := by
  obtain ⟨N, hN⟩ := published_joint_coefficient_volume_bound hCells hHardt hQQE
    (projectionFiber U) (regularPolynomialMap q) (regularPolynomialMap_graph_definable q U hU)
  refine ⟨N, ?_⟩
  intro Z hZ δ hδ hdet Q hQ
  apply hN Z hZ δ hδ _ Q hQ
  intro p hp x hx
  exact ⟨fderiv ℝ (regularPolynomialMap q p) x,
    (differentiable_regularPolynomialMap q p x).hasFDerivAt, hdet p hp x hx⟩

end PaperI
