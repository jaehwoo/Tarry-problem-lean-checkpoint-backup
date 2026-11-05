import PaperILean.GraphDerivativeLoci
import PaperILean.PublishedScalarAnalyticity
import PaperILean.PublishedScalarFiniteFibers
import PaperILean.GraphScalarSlice
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Qualitative Nash regularity supplies finiteness of the actual
nondifferentiability set. Its joint first-order relation then permits the
checked Hardt finite-fiber bound before all real parameters and endpoints.
This is not a uniform bound on nonanalytic points or on analytic subdivisions.
Pre-strategy diagnostics: checkpoint_108_derivative_sign_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
local instance nondifferentiabilityFinTwoDecidableEq : DecidableEq (Fin 2) := Classical.typeDecidableEq _

theorem published_nondifferentiabilitySet_finite
    (hNash : PublishedOneVariableNashRegularity) (f : ℝ → ℝ) (a b : ℝ)
    (hGraph : HasPolynomialSignDescription (openScalarGraph f a b)) :
    (nondifferentiabilitySet f a b).Finite := by
  by_cases hab : a < b
  · obtain ⟨C,_,hA⟩ := hNash.finite_nonanalytic_locus f a b hab hGraph
    apply C.finite_toSet.subset
    intro x hx
    by_contra hxC
    exact hx.2 (hA x hx.1 hxC).differentiableAt
  · apply Set.finite_empty.subset
    intro x hx
    exact (hab (hx.1.1.trans hx.1.2)).elim

theorem scalar_nondifferentiability_fiber_eq {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) :
    scalarProjectionFiber (graphNondifferentiabilityRelation G) (Sum.elim p ![a,b]) =
      nondifferentiabilitySet f a b := by
  ext x
  exact graphNondifferentiabilityRelation_realize_iff G p f a b x hG

/-- N precedes every graph parameter, represented function and endpoint.
Finiteness is asserted separately from the natural-cardinality bound. -/
theorem published_uniform_nondifferentiability_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ N : ℕ, ∀ (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ),
      (∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) →
      (nondifferentiabilitySet f a b).Finite ∧ Nat.card (nondifferentiabilitySet f a b) ≤ N := by
  obtain ⟨N,hN⟩ := published_scalar_finite_fiber_card_bound hCell hHardt hQE
    (graphNondifferentiabilityRelation G)
    (hQE.finite_sign_description _ (graphNondifferentiabilityRelation_definable hG))
  refine ⟨N,?_⟩
  intro p f a b hrep
  have hfin := published_nondifferentiabilitySet_finite hNash f a b
    (published_openScalarGraph_sign_description hQE hG p f a b hrep)
  have he := scalar_nondifferentiability_fiber_eq G p f a b hrep
  refine ⟨hfin,?_⟩
  have hb := hN (Sum.elim p ![a,b]) (he.symm ▸ hfin)
  simpa only [he] using hb

theorem published_bounded_tuple_nondifferentiability_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    (s D : ℕ) :
    ∃ N : ℕ, ∀ (P : Fin s → MvPolynomial (Fin 2) ℝ),
      (∀ i, (P i).totalDegree ≤ D) → ∀ S : Set (Fin 2 → ℝ),
      PolynomialSignDetermined (Finset.univ.image P) S →
      ∀ (f : ℝ → ℝ) (a b : ℝ),
      (∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      (nondifferentiabilitySet f a b).Finite ∧ Nat.card (nondifferentiabilitySet f a b) ≤ N := by
  classical
  have h := fun q : (Fin s → Bool × Bool) → Bool =>
    published_uniform_nondifferentiability_bound hCell hHardt hQE hNash
      (universalPolynomialBooleanSet (Fin 2) s D q)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s D q))
  choose N hN using h
  refine ⟨Finset.univ.sup N,?_⟩
  intro P hP S hS f a b hrep
  obtain ⟨q,hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D P hP S hS
  have hrep' : ∀ t ∈ Icc a b, ∀ y : ℝ,
      Sum.elim (polynomialFamilyCoefficients D P) ![t,y] ∈
        universalPolynomialBooleanSet (Fin 2) s D q ↔ y = f t := by
    intro t ht y
    simpa only [hEq,mem_setOf_eq] using hrep t ht y
  obtain ⟨hf,hc⟩ := hN q (polynomialFamilyCoefficients D P) f a b hrep'
  exact ⟨hf,hc.trans (Finset.le_sup (f := N) (Finset.mem_univ q))⟩

/-- At-most graph sign format, including repeated atoms and degree drops. -/
theorem published_bounded_sign_format_nondifferentiability_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    (s D : ℕ) :
    ∃ N : ℕ, ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ P ∈ A, P.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ (f : ℝ → ℝ) (a b : ℝ),
      (∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      (nondifferentiabilitySet f a b).Finite ∧ Nat.card (nondifferentiabilitySet f a b) ≤ N := by
  obtain ⟨N,hN⟩ := published_bounded_tuple_nondifferentiability_bound hCell hHardt hQE hNash s D
  refine ⟨N,?_⟩
  intro A S hcard hdeg hS f a b hrep
  obtain ⟨P,hP,hSP⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hcard hdeg hS
  exact hN P hP S hSP f a b hrep

end PaperI
