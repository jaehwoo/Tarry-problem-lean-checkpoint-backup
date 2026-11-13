import PaperILean.AnalyticGraphPieces
import PaperILean.FiniteExceptionalCuts

/-! The checked count consequence of finitely many joint analytic pieces and
uniform bounds on their actual scalar frontiers. The later published wrapper
proves these prerequisites from qualitative Nash decomposition and Hardt. -/

noncomputable section
namespace PaperI
open Set
open scoped BigOperators

/-- Analyticity on consecutive open intervals; endpoint analyticity is absent. -/
def AnalyticOnCutIntervals (f : ℝ → ℝ) (C : Finset ℝ) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
    AnalyticOnNhd ℝ f (Ioo u v)

/-- The actual piece frontier bounds are fixed before the parameter, function,
and both endpoints. No continuity outside or at the endpoints is used. -/
theorem uniform_analytic_cuts_of_piece_frontier_bounds
    {α : Type} [Fintype α] (G : Set ((α ⊕ Fin 2) → ℝ))
    {n : ℕ} (V : Fin n → Set ((α ⊕ Unit) → ℝ))
    (hExt : ∀ i, HasLocalAnalyticExtensionOn
      (uniqueGraphValue (scalarGraphAsUnit G)) (V i))
    (hCover : ∀ z ∈ uniqueGraphDomain (scalarGraphAsUnit G), ∃ i, z ∈ V i)
    (N : Fin n → ℕ)
    (hFin : ∀ i p, (frontier (scalarProjectionFiber (V i) p)).Finite)
    (hBound : ∀ i p, Nat.card (frontier (scalarProjectionFiber (V i) p)) ≤ N i) :
    ∃ K : ℕ, ∀ (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        AnalyticOnCutIntervals f C ∧ C.card ≤ K := by
  refine ⟨2 + ∑ i, N i, ?_⟩
  intro p f a b hab hrep
  obtain ⟨C,ha,hb,hC,hcard,hAvoid⟩ := exists_interval_cut_set_of_finite_bad_sets
    (fun i => frontier (scalarProjectionFiber (V i) p)) N
    (fun i => hFin i p) (fun i => hBound i p) hab
  refine ⟨C,ha,hb,hC,?_,hcard⟩
  intro u hu v hv huv hgap
  apply analyticOnNhd_of_unique_graph_piece_frontiers G V hExt hCover p f a b u v hrep
  · intro x hx
    exact ⟨(hC u hu).1.trans hx.1.le,hx.2.le.trans (hC v hv).2⟩
  · exact hAvoid u hu v hv huv hgap

end PaperI
