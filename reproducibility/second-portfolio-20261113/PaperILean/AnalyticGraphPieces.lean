import PaperILean.PublishedPiecewiseNashExtensions

/-! Actual interval realization of analyticity from finite pieces of the joint
unique-output graph domain. The function may be arbitrary outside its stated
closed interval. Frontier avoidance is an explicit local prerequisite here;
its uniform construction is proved in the following application module. -/

noncomputable section
namespace PaperI
open Set Filter
open scoped Topology

/-- Every point of an open interval belongs locally to one analytic piece of
the canonical graph value. Exact interval graph correctness transfers that
local analytic germ to the represented function. -/
theorem analyticOnNhd_of_unique_graph_piece_frontiers
    {α : Type} [Fintype α] (G : Set ((α ⊕ Fin 2) → ℝ))
    {n : ℕ} (V : Fin n → Set ((α ⊕ Unit) → ℝ))
    (hExt : ∀ i, HasLocalAnalyticExtensionOn
      (uniqueGraphValue (scalarGraphAsUnit G)) (V i))
    (hCover : ∀ z ∈ uniqueGraphDomain (scalarGraphAsUnit G), ∃ i, z ∈ V i)
    (p : α → ℝ) (f : ℝ → ℝ) (a b u v : ℝ)
    (hrep : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t)
    (hsub : Ioo u v ⊆ Icc a b)
    (hAvoid : ∀ i, ∀ x ∈ Ioo u v,
      x ∉ frontier (scalarProjectionFiber (V i) p)) :
    AnalyticOnNhd ℝ f (Ioo u v) := by
  intro x hx
  have hvalue := uniqueGraphValue_scalar_eq G p x (f x) (hrep x (hsub hx))
  obtain ⟨i,hi⟩ := hCover _ hvalue.1
  have han := analyticAt_scalar_fiber_of_not_mem_frontier (hExt i) p x hi (hAvoid i x hx)
  apply han.congr
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  exact (uniqueGraphValue_scalar_eq G p t (f t) (hrep t (hsub ht))).2

end PaperI
