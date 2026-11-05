import PaperILean.PublishedScalarFiniteFibers
import Mathlib.Analysis.Analytic.Constructions

/-! Checked restriction of a local ambient analytic extension to an analytic
curve lying locally in the represented piece. No published input is introduced
in this module. In particular no topological chart is treated as analytic.
Pre-strategy diagnostics: checkpoint_108_004_analytic_uniformity_obstructions.log. -/

noncomputable section
namespace PaperI
open Set Filter
open scoped Topology

/-- At each point of the piece, the function agrees locally on that piece with
an ambient analytic function. This definition does not assert that the piece
is open, smooth, or semialgebraic. -/
def HasLocalAnalyticExtensionOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (S : Set E) : Prop :=
  ∀ x ∈ S, ∃ g : E → ℝ, AnalyticAt ℝ g x ∧
    ∀ᶠ z in 𝓝 x, z ∈ S → g z = F z

/-- An analytic curve must genuinely remain in the piece on a neighborhood of
the point; membership at one point alone is insufficient. -/
theorem analyticAt_comp_of_local_analytic_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {S : Set E} (hF : HasLocalAnalyticExtensionOn F S)
    {c : ℝ → E} {t : ℝ} (hc : AnalyticAt ℝ c t)
    (ht : c t ∈ S) (hlocal : ∀ᶠ u in 𝓝 t, c u ∈ S) :
    AnalyticAt ℝ (fun u => F (c u)) t := by
  obtain ⟨g,hg,hEq⟩ := hF (c t) ht
  apply (hg.comp hc).congr
  filter_upwards [hc.continuousAt.eventually hEq, hlocal] with u hu hSu
  exact hu hSu

/-- The parameter is held fixed while the scalar coordinate varies. -/
theorem analyticAt_scalar_fiber_line
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (t : ℝ) :
    AnalyticAt ℝ (fun u => Sum.elim p (fun _ : Unit => u)) t := by
  apply AnalyticAt.pi
  intro j
  cases j with
  | inl i => exact analyticAt_const
  | inr u => exact analyticAt_id

/-- Away from the frontier of the actual one-dimensional slice, membership
in a piece supplies the neighborhood needed to restrict its local extension. -/
theorem analyticAt_scalar_fiber_of_not_mem_frontier
    {ι : Type*} [Fintype ι]
    {F : ((ι ⊕ Unit) → ℝ) → ℝ} {S : Set ((ι ⊕ Unit) → ℝ)}
    (hF : HasLocalAnalyticExtensionOn F S) (p : ι → ℝ) (t : ℝ)
    (ht : t ∈ scalarProjectionFiber S p)
    (hb : t ∉ frontier (scalarProjectionFiber S p)) :
    AnalyticAt ℝ (fun u => F (Sum.elim p (fun _ : Unit => u))) t := by
  have hInt : t ∈ interior (scalarProjectionFiber S p) := by
    rw [← self_diff_frontier]
    exact ⟨ht,hb⟩
  exact analyticAt_comp_of_local_analytic_extension hF
    (analyticAt_scalar_fiber_line p t) ht (mem_interior_iff_mem_nhds.mp hInt)

end PaperI
