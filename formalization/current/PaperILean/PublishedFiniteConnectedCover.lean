import PaperILean.FiniteConnectedCover
import PaperILean.PolynomialSignDefinability

/-! A structural consequence of published semialgebraic cell decomposition.

Basu--Pollack--Roy, second edition, Theorem 5.6 and Corollary 5.7 give a
finite cell decomposition adapted to a semialgebraic set. Proposition 5.3 and
Theorem 5.19 identify its cells with open cubes of possibly zero dimension;
over the real numbers these cells are connected (cf. Theorem 5.22). We retain
only a finite preconnected cover of the actual subtype. No component count,
format bound, fiber bound, or dimension assertion is part of this contract.

The published input is an explicit Prop parameter with no supplied inhabitant.
The local conversion from a cover to finite connected components is proved.
The mandatory obstruction tests were executed before this module was written:
checkpoint_103_005_components_obstructions_fixed.log. They include empty
fibers, coefficient vanishing, degree drops, and the infinite Nat.card pitfall.
-/

noncomputable section
namespace PaperI

/-- Qualitative geometric cover input; the integer may depend on the full set. -/
structure PublishedFiniteConnectedCover : Prop where
  finite_preconnected_cover : ∀ {α : Type} [Finite α] (S : Set (α → ℝ)),
    HasPolynomialSignDescription S →
      ∃ (n : ℕ) (U : Fin n → Set S),
        (∀ i, IsPreconnected (U i)) ∧ (∀ x, ∃ i, x ∈ U i)

theorem published_finite_connectedComponents
    (hCell : PublishedFiniteConnectedCover)
    {α : Type} [Finite α] (S : Set (α → ℝ))
    (hS : HasPolynomialSignDescription S) : Finite (ConnectedComponents S) := by
  obtain ⟨n, U, hpre, hcover⟩ := hCell.finite_preconnected_cover S hS
  exact finite_connectedComponents_of_finite_preconnected_cover U hpre hcover

/-- Both actual finiteness and the natural-cardinality bound are retained. -/
theorem published_exists_connectedComponents_bound
    (hCell : PublishedFiniteConnectedCover)
    {α : Type} [Finite α] (S : Set (α → ℝ))
    (hS : HasPolynomialSignDescription S) :
    ∃ N : ℕ, Finite (ConnectedComponents S) ∧ Nat.card (ConnectedComponents S) ≤ N := by
  obtain ⟨n, U, hpre, hcover⟩ := hCell.finite_preconnected_cover S hS
  refine ⟨n, ?_⟩
  simpa using finite_connectedComponents_and_card_le_of_finite_preconnected_cover U hpre hcover

end PaperI
