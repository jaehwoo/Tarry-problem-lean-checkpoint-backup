import PaperILean.PublishedSemialgebraicPaths
import PaperILean.EndpointParameterFamily

/-! Uniform graph format for paths between arbitrary endpoints of any
connected fiber of one joint semialgebraic family. The count and degree are
chosen before the base value, its connectedness proof, and both endpoints.
No assumption that every fiber is connected is imposed. Piecewise analyticity
is a separate assertion and is not included here. -/

noncomputable section
namespace PaperI

theorem published_family_uniform_endpoint_path_format
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {α κ : Type} [Finite α] [Finite κ]
    (A : Set ((α ⊕ κ) → ℝ)) (hA : HasPolynomialSignDescription A) :
    ∃ s d : ℕ, ∀ p : α → ℝ, IsPreconnected (projectionFiber A p) →
      ∀ x ∈ projectionFiber A p, ∀ y ∈ projectionFiber A p,
      ∃ δ : SemialgebraicUnitPath (projectionFiber A p) x y,
      ∃ B : Finset (MvPolynomial (Unit ⊕ κ) ℝ), B.card ≤ s ∧
        (∀ q ∈ B, q.totalDegree ≤ d) ∧
        PolynomialSignDetermined B (unitPathGraph δ.toFun) := by
  obtain ⟨s, d, hs⟩ := published_marked_family_uniform_path_format hPath hHardt hQE
    (endpointParameterizedFamily A)
    (published_endpointParameterizedFamily_sign_description hQE hA)
    endpointValue
    (published_endpointParameterizedFamily_endpointGraph_sign_description hQE hA)
    (endpointValue_mem A)
  refine ⟨s, d, ?_⟩
  intro p hc x hx y hy
  have hb : endpointParameter p x y ∈ projectionDomain (endpointParameterizedFamily A) :=
    (endpointParameterizedFamily_domain A p x y).mpr ⟨hx, hy⟩
  have hconn := endpointParameterizedFamily_preconnected_at A p x y hx hy hc
  obtain ⟨δ, B, hBcard, hBdegree, hB⟩ := hs (endpointParameter p x y) hb hconn
  let δ' : SemialgebraicUnitPath (projectionFiber A p) x y := {
    toFun := δ.toFun
    continuousOn := δ.continuousOn
    mapsTo := by
      rw [← endpointParameterizedFamily_fiber A p x y hx hy]
      exact δ.mapsTo
    source := δ.source.trans (endpointValue_zero p x y)
    target := δ.target.trans (endpointValue_one p x y)
    semialgebraic := δ.semialgebraic }
  exact ⟨δ', B, hBcard, hBdegree, hB⟩

end PaperI
