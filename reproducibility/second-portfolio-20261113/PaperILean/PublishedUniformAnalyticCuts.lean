import PaperILean.FinitePieceAnalyticCuts
import PaperILean.ScalarSemialgebraicFrontier108

/-! Uniform analytic subdivision for a fixed joint semialgebraic scalar graph.
The qualitative Nash pieces are chosen once on the joint unique-output domain;
their scalar frontiers are actually definable and finite. The checked Hardt
finite-fiber bound precedes all real parameters, represented functions and
endpoints. No analytic-locus definability or uniform analytic conclusion is an
external premise. Arbitrary behavior off the represented interval is allowed. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- Original analytic-subdivision prerequisite in fixed-family form. -/
theorem published_uniform_analytic_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedPiecewiseNashExtensions)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ K : ℕ, ∀ (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        AnalyticOnCutIntervals f C ∧ C.card ≤ K := by
  classical
  letI := Fintype.ofFinite α
  obtain ⟨n,V,hV,hCover⟩ := published_unique_graph_finite_analytic_pieces hNash hQE G hG
  have h := fun i : Fin n =>
    published_scalar_fiber_frontier_card_bound hCell hHardt hQE (V i) (hV i).1
  choose N hN using h
  exact uniform_analytic_cuts_of_piece_frontier_bounds G V (fun i => (hV i).2.2)
    hCover N (fun i p => (hN i p).1) (fun i p => (hN i p).2)

end PaperI
