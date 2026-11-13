import PaperILean.PublishedFiniteConnectedCover
import PaperILean.PublishedHardtTriviality
import PaperILean.PublishedRealAlgebraicAssumptions

/-! The local component-count application of cell decomposition and Hardt
triviality in I633/I638. A bound is chosen from finitely many reference fibers
before the external parameter. Empty fibers outside the actual image are
included, and actual finiteness is retained alongside Nat.card.

The first theorem takes structural data and an explicit finite-cell input;
the published wrapper constructs those data with accepted QE and Hardt inputs.
These declarations bound a fixed family. A separate universal coefficient
family is needed before calling the bound uniform over all coefficients of a
fixed format. No zero-dimensionality assertion is supplied or redefined here.
-/

noncomputable section
namespace PaperI

/-- A parameter outside the actual projection has an empty actual fiber. -/
theorem projectionFiber_eq_empty_of_not_mem_domain
    {ι κ : Type*} {A : Set ((ι ⊕ κ) → ℝ)} {p : ι → ℝ}
    (hp : p ∉ projectionDomain A) : projectionFiber A p = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  exact hp ⟨x, hx⟩

/-- Empty fibers contribute zero components; finiteness is not inferred from
Nat.card being zero. -/
theorem finite_components_and_card_zero_of_empty_fiber
    {ι κ : Type*} {A : Set ((ι ⊕ κ) → ℝ)} {p : ι → ℝ}
    (hp : p ∉ projectionDomain A) :
    Finite (ConnectedComponents (projectionFiber A p)) ∧
      Nat.card (ConnectedComponents (projectionFiber A p)) = 0 := by
  let U : Fin 0 → Set (projectionFiber A p) := fun i => Fin.elim0 i
  have hpre : ∀ i, IsPreconnected (U i) := fun i => Fin.elim0 i
  have hcover : ∀ x, ∃ i, x ∈ U i := by
    intro x
    exact (hp ⟨x.val, x.property⟩).elim
  have h := finite_connectedComponents_and_card_le_of_finite_preconnected_cover U hpre hcover
  exact ⟨h.1, Nat.eq_zero_of_le_zero (by simpa using h.2)⟩

namespace ProjectionHardtData

/-- The common integer is selected before every base parameter, including
parameters with empty fibers. It depends on this complete family. -/
theorem exists_uniform_component_bound
    {ι κ : Type} [Finite κ] {A : Set ((ι ⊕ κ) → ℝ)}
    (D : ProjectionHardtData A) (hCell : PublishedFiniteConnectedCover) :
    ∃ N : ℕ, ∀ p : ι → ℝ,
      Finite (ConnectedComponents (projectionFiber A p)) ∧
        Nat.card (ConnectedComponents (projectionFiber A p)) ≤ N := by
  classical
  let c : Fin D.n → ℕ := fun i =>
    Nat.card (ConnectedComponents (projectionFiber A (D.basePoint i).val))
  refine ⟨Finset.univ.sup c, ?_⟩
  intro p
  by_cases hp : p ∈ projectionDomain A
  · obtain ⟨i, hi⟩ := D.cover p hp
    have hf := published_finite_connectedComponents hCell
      (projectionFiber A (D.basePoint i).val) (D.fiber_semialgebraic i)
    have hb : Finite (ConnectedComponents (projectionFiber A (D.basePoint i).val)) ∧
        Nat.card (ConnectedComponents (projectionFiber A (D.basePoint i).val)) ≤
          Finset.univ.sup c := ⟨hf, Finset.le_sup (f := c) (Finset.mem_univ i)⟩
    exact finite_connectedComponents_and_card_le_of_homeomorph
      (D.fiberHomeomorph i ⟨p, hi⟩) hb
  · have h := finite_components_and_card_zero_of_empty_fiber hp
    exact ⟨h.1, h.2.trans_le (Nat.zero_le _)⟩

end ProjectionHardtData

/-- Original cell/triviality application, relative to explicit published
structural inputs. This is a fixed-family bound, not yet a format-only bound. -/
theorem published_projection_fiber_component_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {ι κ : Type} [Finite ι] [Finite κ]
    (A : Set ((ι ⊕ κ) → ℝ)) (hA : HasPolynomialSignDescription A) :
    ∃ N : ℕ, ∀ p : ι → ℝ,
      Finite (ConnectedComponents (projectionFiber A p)) ∧
        Nat.card (ConnectedComponents (projectionFiber A p)) ≤ N := by
  have hdom : HasPolynomialSignDescription (projectionDomain A) :=
    published_real_projection_has_sign_description hQE
      (hasPolynomialSignDescription_definable hA)
  obtain ⟨D⟩ := hHardt.projection_trivialization A hA hdom
  exact D.exists_uniform_component_bound hCell

/-- Finitely many Boolean descriptions can share one bound. The index and
all real base parameters occur after the bound; this is the assembly needed
when a universal coefficient family is built for each Boolean sign pattern. -/
theorem published_finite_family_projection_fiber_component_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {τ ι κ : Type} [Finite τ] [Finite ι] [Finite κ]
    (A : τ → Set ((ι ⊕ κ) → ℝ))
    (hA : ∀ j, HasPolynomialSignDescription (A j)) :
    ∃ N : ℕ, ∀ (j : τ) (p : ι → ℝ),
      Finite (ConnectedComponents (projectionFiber (A j) p)) ∧
        Nat.card (ConnectedComponents (projectionFiber (A j) p)) ≤ N := by
  classical
  letI : Fintype τ := Fintype.ofFinite τ
  choose N hN using fun j =>
    published_projection_fiber_component_bound hCell hHardt hQE (A j) (hA j)
  refine ⟨Finset.univ.sup N, ?_⟩
  intro j p
  exact ⟨(hN j p).1, (hN j p).2.trans (Finset.le_sup (f := N) (Finset.mem_univ j))⟩

/-- A single bound applies to every totally disconnected fiber of the family.
The premise is topological and is not a replacement definition for geometric
semialgebraic dimension zero. -/
theorem published_projection_totallyDisconnected_fiber_card_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {ι κ : Type} [Finite ι] [Finite κ]
    (A : Set ((ι ⊕ κ) → ℝ)) (hA : HasPolynomialSignDescription A) :
    ∃ N : ℕ, ∀ p : ι → ℝ,
      TotallyDisconnectedSpace (projectionFiber A p) →
        Finite (projectionFiber A p) ∧ Nat.card (projectionFiber A p) ≤ N := by
  obtain ⟨N, hN⟩ := published_projection_fiber_component_bound hCell hHardt hQE A hA
  refine ⟨N, ?_⟩
  intro p hp
  letI : TotallyDisconnectedSpace (projectionFiber A p) := hp
  exact finite_and_card_le_of_totallyDisconnected (hN p)

/-- The same topological application after synchronizing finitely many
semialgebraic descriptions. Both description and base parameter follow N. -/
theorem published_finite_family_totallyDisconnected_fiber_card_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {τ ι κ : Type} [Finite τ] [Finite ι] [Finite κ]
    (A : τ → Set ((ι ⊕ κ) → ℝ))
    (hA : ∀ j, HasPolynomialSignDescription (A j)) :
    ∃ N : ℕ, ∀ (j : τ) (p : ι → ℝ),
      TotallyDisconnectedSpace (projectionFiber (A j) p) →
        Finite (projectionFiber (A j) p) ∧ Nat.card (projectionFiber (A j) p) ≤ N := by
  obtain ⟨N, hN⟩ :=
    published_finite_family_projection_fiber_component_bound hCell hHardt hQE A hA
  refine ⟨N, ?_⟩
  intro j p hp
  letI : TotallyDisconnectedSpace (projectionFiber (A j) p) := hp
  exact finite_and_card_le_of_totallyDisconnected (hN j p)

end PaperI
