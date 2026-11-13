import PaperILean.HardtTransportedCells
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple

/-! Uniform descriptions of actual connected components. No new published
contract is introduced. Reference cells give finitely many joint transported
cover members; their common sign family determines every component. -/

noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem published_family_uniform_component_sign_format
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Finite κ]
    (A : Set ((ρ ⊕ κ) → ℝ)) (hA : HasPolynomialSignDescription A) :
    ∃ s d : ℕ, ∀ p : ρ → ℝ, ∃ B : Finset (MvPolynomial κ ℝ),
      B.card ≤ s ∧ (∀ q ∈ B, q.totalDegree ≤ d) ∧
      ∀ z, PolynomialSignDetermined B (connectedComponentIn (projectionFiber A p) z) := by
  classical
  have hdom := published_real_projection_has_sign_description hQE
    (hasPolynomialSignDescription_definable hA)
  obtain ⟨D⟩ := hHardt.projection_trivialization A (fun _ => A) hA hdom
    (fun _ => hA) (fun _ => subset_rfl)
  let c := fun i : Fin D.n => Classical.choice
    (hCell.cell_decomposition (projectionFiber A (D.basePoint i).val) (D.fiber_semialgebraic i))
  let J := Σ i : Fin D.n, Fin (c i).count
  let G : J → Set ((ρ ⊕ κ) → ℝ) :=
    fun j => hardtTransportSet D.toProjectionHardtData j.1 ((c j.1).cell j.2)
  apply finite_semialgebraic_cover_uniform_component_format A G
  · intro j
    exact hQE.finite_sign_description _
      (hardtTransportSet_definable D j.1 ((c j.1).cell_semialgebraic j.2))
  · intro p j
    exact hardtTransportSet_fiber_preconnected D.toProjectionHardtData j.1 _
      ((c j.1).subset j.2) ((c j.1).cell_isPreconnected j.2) p
  · intro p j
    exact hardtTransportSet_fiber_subset D.toProjectionHardtData j.1 _ p
  · intro p x hx
    obtain ⟨i,j,h⟩ := hardtTransportSet_cell_cover D.toProjectionHardtData c p x hx
    exact ⟨⟨i,j⟩,h⟩

/-- The count and degree precede all coefficients and Boolean descriptions.
The same output polynomial family works for every component seed. -/
theorem published_bounded_tuple_component_sign_format
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (α : Type) [Fintype α] (s D : ℕ) :
    ∃ sOut dOut : ℕ, ∀ (p : Fin s → MvPolynomial α ℝ),
      (∀ i, (p i).totalDegree ≤ D) → ∀ S : Set (α → ℝ),
      PolynomialSignDetermined (Finset.univ.image p) S →
      ∃ B : Finset (MvPolynomial α ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ dOut) ∧
        ∀ z, PolynomialSignDetermined B (connectedComponentIn S z) := by
  classical
  have h := fun b : (Fin s → Bool × Bool) → Bool =>
    published_family_uniform_component_sign_format hCell hHardt hQE
      (universalPolynomialBooleanSet α s D b)
      (universalPolynomialBooleanSet_hasPolynomialSignDescription α s D b)
  choose sOut dOut hOut using h
  refine ⟨Finset.univ.sup sOut,Finset.univ.sup dOut,?_⟩
  intro p hp S hS
  obtain ⟨b,hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D p hp S hS
  obtain ⟨B,hBc,hBd,hBS⟩ := hOut b (polynomialFamilyCoefficients D p)
  refine ⟨B,hBc.trans (Finset.le_sup (f := sOut) (Finset.mem_univ b)),
    fun q hq => (hBd q hq).trans (Finset.le_sup (f := dOut) (Finset.mem_univ b)),?_⟩
  simpa only [hEq] using hBS

theorem published_bounded_sign_format_component_sign_format
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (α : Type) [Fintype α] (s D : ℕ) :
    ∃ sOut dOut : ℕ, ∀ (A : Finset (MvPolynomial α ℝ)) (S : Set (α → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∃ B : Finset (MvPolynomial α ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ dOut) ∧
        ∀ z, PolynomialSignDetermined B (connectedComponentIn S z) := by
  obtain ⟨sOut,dOut,h⟩ := published_bounded_tuple_component_sign_format hCell hHardt hQE α s D
  refine ⟨sOut,dOut,?_⟩
  intro A S hc hd hS
  obtain ⟨p,hp,hSp⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hc hd hS
  exact h p hp S hSp

end PaperI
