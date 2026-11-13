import PaperILean.RegularCoefficientFiberPolynomial
import PaperILean.PublishedRealAlgebraicAssumptions
import PaperILean.JointParameterVolume

/-! Joint measurability for the concrete polynomial coefficient-map family.
The external coordinates and active input coordinates remain in the joint
map and selected domain. No measurable-section hypothesis replaces this joint
statement. Empty coordinate types and empty selected domains are allowed.
Pre-strategy: checkpoint_107_fubini_pre_strategy.{py,json}. -/

noncomputable section
open FirstOrder MeasureTheory
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem continuous_sumElim_coordinates {ι κ : Type*} :
    Continuous (fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2) := by
  apply continuous_pi
  intro j
  cases j with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr j => exact (continuous_apply j).comp continuous_snd

/-- All external parameters and input coordinates enter the same polynomial
evaluation, so continuity is joint rather than only slicewise. -/
theorem continuous_regularPolynomialMap_joint {ι κ : Type}
    (q : κ → MvPolynomial (ι ⊕ κ) ℝ) :
    Continuous (fun z : (ι → ℝ) × (κ → ℝ) => regularPolynomialMap q z.1 z.2) := by
  apply continuous_pi
  intro j
  exact (q j).continuous_eval.comp continuous_sumElim_coordinates

theorem measurable_regularPolynomialMap_joint {ι κ : Type}
    [Fintype ι] [Fintype κ] (q : κ → MvPolynomial (ι ⊕ κ) ℝ) :
    Measurable (fun z : (ι → ℝ) × (κ → ℝ) => regularPolynomialMap q z.1 z.2) :=
  (continuous_regularPolynomialMap_joint q).measurable

/-- A sign description supplies actual Borel measurability of the full
selected domain; the Sum coordinates are identified with the product. -/
theorem measurableSet_joint_domain_of_sign_description {ι κ : Type}
    [Fintype ι] [Fintype κ] (U : Set ((ι ⊕ κ) → ℝ))
    (hU : HasPolynomialSignDescription U) :
    MeasurableSet {z : (ι → ℝ) × (κ → ℝ) | Sum.elim z.1 z.2 ∈ U} := by
  have hB : MeasurableSet U := by
    convert hasPolynomialSignDescription_borel hU
    exact BorelSpace.measurable_eq
  exact continuous_sumElim_coordinates.measurable hB

/-- Qualitative QE is the only accepted input used to obtain a joint Borel
domain from its actual first-order definition. -/
theorem published_measurableSet_joint_domain
    (hQE : PublishedRealSemialgebraicity) {ι κ : Type}
    [Fintype ι] [Fintype κ] (U : Set ((ι ⊕ κ) → ℝ))
    (hU : (Set.univ : Set ℝ).Definable Language.ring U) :
    MeasurableSet {z : (ι → ℝ) × (κ → ℝ) | Sum.elim z.1 z.2 ∈ U} :=
  measurableSet_joint_domain_of_sign_description U (hQE.finite_sign_description U hU)

/-- The polynomial selected output region is jointly measurable. This is the
measurability input needed for the later Fubini application, not a slice volume
estimate or a claim that downstream branches have already been identified. -/
theorem published_measurableSet_joint_regularPolynomial_preimage
    (hQE : PublishedRealSemialgebraicity) {ι κ : Type}
    [Fintype ι] [Fintype κ] (q : κ → MvPolynomial (ι ⊕ κ) ℝ)
    (U : Set ((ι ⊕ κ) → ℝ))
    (hU : (Set.univ : Set ℝ).Definable Language.ring U)
    (Q : Set (κ → ℝ)) (hQ : MeasurableSet Q) :
    MeasurableSet {z : (ι → ℝ) × (κ → ℝ) |
      Sum.elim z.1 z.2 ∈ U ∧ regularPolynomialMap q z.1 z.2 ∈ Q} :=
  (published_measurableSet_joint_domain hQE U hU).inter
    (measurable_regularPolynomialMap_joint q hQ)

end PaperI
