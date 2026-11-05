import PaperILean.FiniteConnectedCover
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! I665: a nonzero square Jacobian makes each selected fiber discrete.
The derivative is an ambient derivative at each selected point. The selected
domain itself need not be open, and no global injectivity is concluded.
The argument uses the first-order remainder estimate already in mathlib;
it needs neither a global inverse nor an extra continuous-derivative premise.
Pre-strategy evidence: checkpoint 106 record 003. -/

noncomputable section
open scoped Topology
open Set Filter
namespace PaperI

/-- A pointwise derivative bounded below isolates that point in the actual
selected fiber. The lower-bound constant may depend on the selected point. -/
theorem discrete_regularCoefficientFiber_of_derivative_lowerBound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (Ω : Set E) (y : F)
    (hf : ∀ x ∈ Ω, ∃ L : E →L[ℝ] F,
      HasFDerivAt f L x ∧ ∃ C : ℝ, ∀ z, ‖z‖ ≤ C * ‖L z‖) :
    DiscreteTopology {x : E | x ∈ Ω ∧ f x = y} := by
  rw [discreteTopology_subtype_iff]
  intro x hx
  rw [Filter.inf_principal_eq_bot]
  obtain ⟨L, hL, hbound⟩ := hf x hx.1
  have hne : ∀ᶠ z in 𝓝[≠] x, f z ≠ y := hL.eventually_ne hbound
  exact hne.mono (fun z hz hmem => hz hmem.2)

/-- Invertibility is used only to obtain a local linear lower bound. -/
theorem discrete_regularCoefficientFiber_of_equiv_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (Ω : Set E) (y : F)
    (hf : ∀ x ∈ Ω, ∃ L : E ≃L[ℝ] F, HasFDerivAt f (L : E →L[ℝ] F) x) :
    DiscreteTopology {x : E | x ∈ Ω ∧ f x = y} := by
  apply discrete_regularCoefficientFiber_of_derivative_lowerBound f Ω y
  intro x hx
  obtain ⟨L, hL⟩ := hf x hx
  refine ⟨L, hL, ‖(L.symm : F →L[ℝ] E)‖, ?_⟩
  intro z
  simpa using (L.symm : F →L[ℝ] E).le_opNorm (L z)

/-- The manuscript's square-Jacobian condition, in its invariant determinant
form, supplies the required derivative equivalence. -/
theorem discrete_regularCoefficientFiber_of_det_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → E) (Ω : Set E) (y : E)
    (hf : ∀ x ∈ Ω, ∃ L : E →L[ℝ] E, HasFDerivAt f L x ∧ L.det ≠ 0) :
    DiscreteTopology {x : E | x ∈ Ω ∧ f x = y} := by
  apply discrete_regularCoefficientFiber_of_equiv_derivative f Ω y
  intro x hx
  obtain ⟨L, hL, hdet⟩ := hf x hx
  exact ⟨L.toContinuousLinearEquivOfDetNeZero hdet, by simpa using hL⟩

/-- Once component finiteness and its bound have been supplied independently,
the discrete selected fiber has the same cardinality bound. -/
theorem finite_regularCoefficientFiber_of_det_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → E) (Ω : Set E) (y : E)
    (hf : ∀ x ∈ Ω, ∃ L : E →L[ℝ] E, HasFDerivAt f L x ∧ L.det ≠ 0)
    {N : ℕ} (hN : Finite (ConnectedComponents {x : E | x ∈ Ω ∧ f x = y}) ∧
      Nat.card (ConnectedComponents {x : E | x ∈ Ω ∧ f x = y}) ≤ N) :
    Finite {x : E | x ∈ Ω ∧ f x = y} ∧ Nat.card {x : E | x ∈ Ω ∧ f x = y} ≤ N := by
  letI := discrete_regularCoefficientFiber_of_det_ne_zero f Ω y hf
  exact finite_and_card_le_of_totallyDisconnected hN

end PaperI
