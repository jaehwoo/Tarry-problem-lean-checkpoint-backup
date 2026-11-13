import PaperILean.IteratedDerivativeLoci
import PaperILean.PublishedScalarFiniteFibers
import PaperILean.BoundedPolynomialTuple
import PaperILean.UniversalSignFamily

/-! Original preparation, I949: the signed derivative superlevel sets have
uniformly bounded component counts. Every derivative order up to a fixed N
shares one count, chosen before graph coefficients, function, interval, sign
and threshold. This is the component-count prerequisite, not a measure bound.
Accepted QE, finite cells and Hardt are explicit inputs. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
local instance superlevelFinTwoDecidableEq : DecidableEq (Fin 2) := Classical.typeDecidableEq _

def projectionFiberUnitHomeomorphScalar {ι : Type*} (A : Set ((ι ⊕ Unit) → ℝ))
    (p : ι → ℝ) : projectionFiber A p ≃ₜ scalarProjectionFiber A p where
  toEquiv := projectionFiberUnitEquivScalar A p
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply ()).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun _ => continuous_subtype_val)

theorem published_uniform_iteratedDerivative_superlevel_components
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) (N : ℕ) :
    ∃ K : ℕ, ∀ (p : α → ℝ) (f : ℝ → ℝ) (a b threshold sign : ℝ),
      (∀ t ∈ Ioo a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) →
      ContDiffOn ℝ N f (Ioo a b) → ∀ n ≤ N,
      Finite (ConnectedComponents (signedIteratedDerivativeSuperlevel f n a b threshold sign)) ∧
        Nat.card (ConnectedComponents (signedIteratedDerivativeSuperlevel f n a b threshold sign)) ≤ K := by
  obtain ⟨K,hK⟩ := published_finite_family_projection_fiber_component_bound
    hCell hHardt hQE (fun n : Fin (N+1) => iteratedDerivativeSuperlevelRelation G n.val)
    (fun n => hQE.finite_sign_description _ (iteratedDerivativeSuperlevelRelation_definable hG n.val))
  refine ⟨K,?_⟩
  intro p f a b threshold sign hrep hf n hn
  have h := finite_connectedComponents_and_card_le_of_homeomorph
    (projectionFiberUnitHomeomorphScalar (iteratedDerivativeSuperlevelRelation G n)
      (Sum.elim p ![a,b,threshold,sign]))
    (hK ⟨n,Nat.lt_succ_iff.mpr hn⟩ (Sum.elim p ![a,b,threshold,sign]))
  have he : scalarProjectionFiber (iteratedDerivativeSuperlevelRelation G n)
      (Sum.elim p ![a,b,threshold,sign]) =
        signedIteratedDerivativeSuperlevel f n a b threshold sign := by
    ext x
    exact iteratedDerivativeSuperlevelRelation_realize_iff G p f a b threshold sign N n hrep hf hn x
  exact he ▸ h

theorem published_bounded_tuple_iteratedDerivative_superlevel_components
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s D N : ℕ) :
    ∃ K : ℕ, ∀ (P : Fin s → MvPolynomial (Fin 2) ℝ),
      (∀ i, (P i).totalDegree ≤ D) → ∀ S : Set (Fin 2 → ℝ),
      PolynomialSignDetermined (Finset.univ.image P) S →
      ∀ (f : ℝ → ℝ) (a b threshold sign : ℝ),
      (∀ t ∈ Ioo a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      ContDiffOn ℝ N f (Ioo a b) → ∀ n ≤ N,
      Finite (ConnectedComponents (signedIteratedDerivativeSuperlevel f n a b threshold sign)) ∧
        Nat.card (ConnectedComponents (signedIteratedDerivativeSuperlevel f n a b threshold sign)) ≤ K := by
  classical
  have h := fun q : (Fin s → Bool × Bool) → Bool =>
    published_uniform_iteratedDerivative_superlevel_components hCell hHardt hQE
      (universalPolynomialBooleanSet (Fin 2) s D q)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s D q)) N
  choose K hK using h
  refine ⟨Finset.univ.sup K,?_⟩
  intro P hP S hS f a b threshold sign hrep hf n hn
  obtain ⟨q,hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D P hP S hS
  have hrep' : ∀ t ∈ Ioo a b, ∀ y : ℝ,
      Sum.elim (polynomialFamilyCoefficients D P) ![t,y] ∈
        universalPolynomialBooleanSet (Fin 2) s D q ↔ y = f t := by
    intro t ht y
    simpa only [hEq,mem_setOf_eq] using hrep t ht y
  have hb := hK q (polynomialFamilyCoefficients D P) f a b threshold sign hrep' hf n hn
  exact ⟨hb.1,hb.2.trans (Finset.le_sup (f := K) (Finset.mem_univ q))⟩

theorem published_bounded_sign_format_iteratedDerivative_superlevel_components
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s D N : ℕ) :
    ∃ K : ℕ, ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ P ∈ A, P.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ (f : ℝ → ℝ) (a b threshold sign : ℝ),
      (∀ t ∈ Ioo a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      ContDiffOn ℝ N f (Ioo a b) → ∀ n ≤ N,
      Finite (ConnectedComponents (signedIteratedDerivativeSuperlevel f n a b threshold sign)) ∧
        Nat.card (ConnectedComponents (signedIteratedDerivativeSuperlevel f n a b threshold sign)) ≤ K := by
  obtain ⟨K,hK⟩ := published_bounded_tuple_iteratedDerivative_superlevel_components hCell hHardt hQE s D N
  refine ⟨K,?_⟩
  intro A S hcard hdeg hS f a b threshold sign hrep hf n hn
  obtain ⟨P,hP,hSP⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hcard hdeg hS
  exact hK P hP S hSP f a b threshold sign hrep hf n hn

end PaperI
