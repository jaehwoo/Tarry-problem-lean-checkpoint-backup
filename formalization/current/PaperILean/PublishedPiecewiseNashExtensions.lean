import PaperILean.AnalyticPieceFiber
import PaperILean.SingleValuedGraphDomain

/-! Accepted qualitative structural input, encoded as a weaker CONSEQUENCE of
Fernando--Gamboa--Ruiz, JEMS 16 (2014), §2.4.2 (printed p.545).
A semialgebraic scalar function on an arbitrary semialgebraic domain has a
finite partition into affine Nash manifolds on which its restrictions are Nash.
For the local extension encoding used here, §2.1.4 (p.542) supplies local
ambient Nash flattening coordinates, and §2.7 (p.546) identifies Nash germs
as analytic germs. In tangential coordinates extend the scalar readout by
ignoring normal coordinates, then compose with the ambient chart. This gives
a local ambient analytic extension agreeing on the original piece.
The same argument includes zero-dimensional pieces (constant readout).
No piece-count, coefficient-uniform count, fiber count, cut set, or analytic
bad-locus definability is supplied by this input. The sets need not be open.
No global axiom or inhabitant is added. Source consequence approved after
root primary-source review; exact trust boundary recorded in 108 evidence. -/

noncomputable section
namespace PaperI
open Set
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

structure PublishedPiecewiseNashExtensions : Prop where
  finite_analytic_pieces : ∀ (κ : Type) [Fintype κ]
    (F : (κ → ℝ) → ℝ) (S : Set (κ → ℝ)),
    HasPolynomialSignDescription
      {v : (κ ⊕ Unit) → ℝ | v ∘ Sum.inl ∈ S ∧ v (Sum.inr ()) = F (v ∘ Sum.inl)} →
    ∃ (n : ℕ) (V : Fin n → Set (κ → ℝ)),
      (∀ i, HasPolynomialSignDescription (V i) ∧ V i ⊆ S ∧
        HasLocalAnalyticExtensionOn F (V i)) ∧
      ∀ x ∈ S, ∃ i, x ∈ V i

/-- The qualitative decomposition is applied once to the unique-output part
of the fixed JOINT graph. No parameter or represented function has yet been
chosen. Empty and nonfunctional parts of the original relation are allowed. -/
theorem published_unique_graph_finite_analytic_pieces
    (hNash : PublishedPiecewiseNashExtensions)
    (hQE : PublishedRealSemialgebraicity)
    {α : Type} [Fintype α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable FirstOrder.Language.ring G) :
    ∃ (n : ℕ) (V : Fin n → Set ((α ⊕ Unit) → ℝ)),
      (∀ i, HasPolynomialSignDescription (V i) ∧
        V i ⊆ uniqueGraphDomain (scalarGraphAsUnit G) ∧
        HasLocalAnalyticExtensionOn (uniqueGraphValue (scalarGraphAsUnit G)) (V i)) ∧
      ∀ x ∈ uniqueGraphDomain (scalarGraphAsUnit G), ∃ i, x ∈ V i := by
  have hsign := hQE.finite_sign_description _
    (uniqueGraphRelation_definable (scalarGraphAsUnit_definable hG))
  rw [uniqueGraphRelation_eq_graph] at hsign
  exact hNash.finite_analytic_pieces _ _ _ hsign

end PaperI
