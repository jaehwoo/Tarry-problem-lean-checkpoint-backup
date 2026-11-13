import PaperILean.PublishedSemialgebraicSelection
import PaperILean.PolynomialJointMeasurability

/-! Borel measurability on the actual selected domain follows from the actual
single-valued definable graph. Values of a map off its selected domain are
irrelevant. This supplies the joint measurability needed in I666 for implicit
as well as polynomial maps; actual downstream graph identification is separate.

Pre-strategy diagnostics test the failure of sectionwise measurability and the
need for graph uniqueness before identifying a selector with a given map. -/

noncomputable section
open FirstOrder MeasureTheory
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def selectedFunctionGraph {ι κ : Type*} (U : Set (ι → ℝ))
    (f : (ι → ℝ) → (κ → ℝ)) : Set ((ι ⊕ κ) → ℝ) :=
  {v | (fun i => v (Sum.inl i)) ∈ U ∧
    f (fun i => v (Sum.inl i)) = (fun j => v (Sum.inr j))}

theorem projectionDomain_selectedFunctionGraph {ι κ : Type*}
    (U : Set (ι → ℝ)) (f : (ι → ℝ) → (κ → ℝ)) :
    projectionDomain (selectedFunctionGraph U f) = U := by
  ext p
  simp [projectionDomain, selectedFunctionGraph]

/-- Definability of a single-valued selected graph gives definability of its
exact domain, including empty domains. -/
theorem selectedFunctionGraph_domain_definable {ι κ : Type}
    [Finite ι] [Finite κ] (U : Set (ι → ℝ)) (f : (ι → ℝ) → (κ → ℝ))
    (hG : (Set.univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U f)) :
    (Set.univ : Set ℝ).Definable Language.ring U := by
  have h := realDefinable_exists hG
  change (Set.univ : Set ℝ).Definable Language.ring
    (projectionDomain (selectedFunctionGraph U f)) at h
  rwa [projectionDomain_selectedFunctionGraph] at h

/-- The Borel selector agrees with the actual function by graph uniqueness.
Only the restriction to U is asserted measurable. -/
theorem published_measurable_selected_function
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (U : Set (ι → ℝ)) (f : (ι → ℝ) → (κ → ℝ))
    (hG : (Set.univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U f)) :
    Measurable (fun p : U => f p.val) := by
  obtain ⟨σ, hσ, hmem⟩ := published_semialgebraic_borel_selection hQE hHardt
    (selectedFunctionGraph U f) (hQE.finite_sign_description _ hG)
  let e : U → projectionDomain (selectedFunctionGraph U f) := fun p =>
    ⟨p.val, by rw [projectionDomain_selectedFunctionGraph]; exact p.property⟩
  have he : Measurable e := measurable_subtype_coe.subtype_mk
  have hsame : (fun p : U => f p.val) = σ ∘ e := by
    funext p
    exact (hmem (e p)).2
  rw [hsame]
  exact hσ.comp he

/-- Every Borel output set has a Borel preimage inside the exact selected
domain, with no global extension hypothesis on f. -/
theorem published_measurableSet_selected_preimage
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (U : Set (ι → ℝ)) (f : (ι → ℝ) → (κ → ℝ))
    (hG : (Set.univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U f))
    (Q : Set (κ → ℝ)) (hQ : MeasurableSet Q) :
    MeasurableSet {p | p ∈ U ∧ f p ∈ Q} := by
  have hU : MeasurableSet U := by
    convert hasPolynomialSignDescription_borel (hQE.finite_sign_description _
      (selectedFunctionGraph_domain_definable U f hG))
    exact BorelSpace.measurable_eq
  have hpre := published_measurable_selected_function hQE hHardt U f hG hQ
  have himage := hU.subtype_image hpre
  convert himage using 1
  ext p
  simp [and_comm]

/-- The original coefficient graph places output before input. The explicit
coordinate permutation below yields measurability of the actual joint selected
preimage while retaining all external coordinates. -/
theorem published_measurableSet_joint_coefficient_preimage
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (Ω : (ι → ℝ) → Set (κ → ℝ))
    (T : (ι → ℝ) → (κ → ℝ) → (κ → ℝ))
    (hG : (Set.univ : Set ℝ).Definable Language.ring (regularCoefficientGraph Ω T))
    (Q : Set (κ → ℝ)) (hQ : MeasurableSet Q) :
    MeasurableSet {z : (ι → ℝ) × (κ → ℝ) | z.2 ∈ Ω z.1 ∧ T z.1 z.2 ∈ Q} := by
  let U : Set ((ι ⊕ κ) → ℝ) :=
    {v | (fun j => v (Sum.inr j)) ∈ Ω (fun i => v (Sum.inl i))}
  let f : ((ι ⊕ κ) → ℝ) → (κ → ℝ) :=
    fun v => T (fun i => v (Sum.inl i)) (fun j => v (Sum.inr j))
  let e : ((ι ⊕ κ) ⊕ κ) → ((ι ⊕ κ) ⊕ κ) :=
    Sum.elim (Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr)
      (fun j => Sum.inl (Sum.inr j))
  have hsel : (Set.univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U f) := by
    convert hG.preimage_comp e using 1
  have hm := published_measurableSet_selected_preimage hQE hHardt U f hsel Q hQ
  exact continuous_sumElim_coordinates.measurable hm

end PaperI
