import PaperILean.PublishedUniformComponents
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple

/-! Coefficient-uniform component bounds for bounded polynomial sign format.

For fixed coordinate type, number of polynomials, and degree bound, a universal
coefficient family is built for every Boolean sign table. There are finitely
many tables. Cell decomposition and Hardt triviality applied to these families
therefore choose one integer before every actual polynomial coefficient and
before the selected semialgebraic set. Degree drops and zero polynomials need
no exceptional assumptions. This proves qualitative uniformity; it supplies
no explicit numerical bound and does not formalize quantitative QE for an
arbitrary quantified first-order input format.
-/

noncomputable section
namespace PaperI
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- One bound for all coefficient tuples and all Boolean sign descriptions of
s polynomials of total degree at most D in the fixed real coordinate space. -/
theorem published_bounded_tuple_component_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (α : Type) [Fintype α] (s D : ℕ) :
    ∃ N : ℕ, ∀ (p : Fin s → MvPolynomial α ℝ),
      (∀ i, (p i).totalDegree ≤ D) → ∀ S : Set (α → ℝ),
      PolynomialSignDetermined (Finset.univ.image p) S →
        Finite (ConnectedComponents S) ∧ Nat.card (ConnectedComponents S) ≤ N := by
  classical
  obtain ⟨N, hN⟩ := published_finite_family_projection_fiber_component_bound hCell hHardt hQE
    (universalPolynomialBooleanSet α s D)
    (universalPolynomialBooleanSet_hasPolynomialSignDescription α s D)
  refine ⟨N, ?_⟩
  intro p hp S hS
  obtain ⟨b, hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D p hp S hS
  rw [hEq]
  exact hN b (polynomialFamilyCoefficients D p)

/-- The topological finite-fiber consequence with exactly the same
coefficient-uniform bound. Geometric dimension zero remains a separate bridge. -/
theorem published_bounded_tuple_totallyDisconnected_card_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (α : Type) [Fintype α] (s D : ℕ) :
    ∃ N : ℕ, ∀ (p : Fin s → MvPolynomial α ℝ),
      (∀ i, (p i).totalDegree ≤ D) → ∀ S : Set (α → ℝ),
      PolynomialSignDetermined (Finset.univ.image p) S →
      TotallyDisconnectedSpace S → Finite S ∧ Nat.card S ≤ N := by
  obtain ⟨N, hN⟩ := published_bounded_tuple_component_bound hCell hHardt hQE α s D
  refine ⟨N, ?_⟩
  intro p hp S hS hTD
  letI : TotallyDisconnectedSpace S := hTD
  exact finite_and_card_le_of_totallyDisconnected (hN p hp S hS)

/-- Bounded quantifier-free polynomial sign format: N depends on the coordinate
space, s, and D, and precedes the polynomial collection, all its real
coefficients, and the chosen Boolean combination. The count condition is ≤ s. -/
theorem published_bounded_sign_format_component_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (α : Type) [Fintype α] (s D : ℕ) :
    ∃ N : ℕ, ∀ (A : Finset (MvPolynomial α ℝ)) (S : Set (α → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) →
      PolynomialSignDetermined A S →
        Finite (ConnectedComponents S) ∧ Nat.card (ConnectedComponents S) ≤ N := by
  obtain ⟨N, hN⟩ := published_bounded_tuple_component_bound hCell hHardt hQE α s D
  refine ⟨N, ?_⟩
  intro A S hcard hdegree hS
  obtain ⟨p, hp, hSp⟩ :=
    exists_bounded_polynomial_tuple_of_signDetermined A S s D hcard hdegree hS
  exact hN p hp S hSp

/-- The cardinality bound at the same fixed sign format, conditional on the
actual totally-disconnected topology of the selected set. -/
theorem published_bounded_sign_format_totallyDisconnected_card_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (α : Type) [Fintype α] (s D : ℕ) :
    ∃ N : ℕ, ∀ (A : Finset (MvPolynomial α ℝ)) (S : Set (α → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) →
      PolynomialSignDetermined A S → TotallyDisconnectedSpace S →
        Finite S ∧ Nat.card S ≤ N := by
  obtain ⟨N, hN⟩ := published_bounded_sign_format_component_bound hCell hHardt hQE α s D
  refine ⟨N, ?_⟩
  intro A S hcard hdegree hS hTD
  letI : TotallyDisconnectedSpace S := hTD
  exact finite_and_card_le_of_totallyDisconnected (hN A S hcard hdegree hS)

/-- The standard at-most format statement: one integer depends only on the
bounds n₀, s, D, before dimension n ≤ n₀, coefficients, and Boolean description. -/
theorem published_at_most_sign_format_component_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (n₀ s D : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≤ n₀ →
      ∀ (A : Finset (MvPolynomial (Fin n) ℝ)) (S : Set (Fin n → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) →
      PolynomialSignDetermined A S →
        Finite (ConnectedComponents S) ∧ Nat.card (ConnectedComponents S) ≤ N := by
  classical
  choose N hN using fun n : Fin (n₀ + 1) =>
    published_bounded_sign_format_component_bound hCell hHardt hQE (Fin n.val) s D
  refine ⟨Finset.univ.sup N, ?_⟩
  intro n hn A S hcard hdegree hS
  let j : Fin (n₀ + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have h := hN j A S hcard hdegree hS
  exact ⟨h.1, h.2.trans (Finset.le_sup (f := N) (Finset.mem_univ j))⟩

end PaperI
