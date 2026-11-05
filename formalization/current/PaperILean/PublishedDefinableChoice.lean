import PaperILean.SelectedGraphMeasurability

/-! Accepted qualitative semialgebraic choice: Lerario--Rizzi--Tiberio,
Quantitative approximate definable choices, Math. Ann. (2025), Corollary 10,
whose proof treats arbitrary semialgebraic sets (not only compact sets).
This is exact choice, not their approximate-choice Theorems A/B.
The selector is extended arbitrarily outside the projection domain; only its
restricted graph is asserted semialgebraic. No continuity, curve, radius,
path-connectedness, or format bound is included. No inhabitant is supplied. -/

noncomputable section
namespace PaperI

structure PublishedSemialgebraicDefinableChoice : Prop where
  section_exists : ∀ {ρ κ : Type} [Finite ρ] [Finite κ]
    (A : Set ((ρ ⊕ κ) → ℝ)), HasPolynomialSignDescription A →
    ∃ f : (ρ → ℝ) → (κ → ℝ),
      HasPolynomialSignDescription (selectedFunctionGraph (projectionDomain A) f) ∧
      ∀ p ∈ projectionDomain A, Sum.elim p (f p) ∈ A

end PaperI
