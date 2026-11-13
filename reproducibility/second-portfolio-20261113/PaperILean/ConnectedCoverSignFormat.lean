import PaperILean.SemialgebraicRelationComposition
import Mathlib.Topology.Connected.Basic

/-! A common sign family for a preconnected cover determines every actual
connected component. The cover need not be disjoint or relatively closed. -/

noncomputable section
namespace PaperI
open Set

theorem preconnected_cover_member_subset_component {X ι : Type*} [TopologicalSpace X]
    {S : Set X} {U : ι → Set X} (hpre : ∀ i, IsPreconnected (U i))
    (hsub : ∀ i, U i ⊆ S) {z x : X} {i : ι}
    (hx : x ∈ connectedComponentIn S z) (hxi : x ∈ U i) :
    U i ⊆ connectedComponentIn S z := by
  have h := (hpre i).subset_connectedComponentIn hxi (hsub i)
  rwa [← connectedComponentIn_eq hx] at h

theorem polynomialSignDetermined_component_of_preconnected_cover
    {α ι : Type*} (B : Finset (MvPolynomial α ℝ))
    (S : Set (α → ℝ)) (U : ι → Set (α → ℝ))
    (hpre : ∀ i, IsPreconnected (U i)) (hsub : ∀ i, U i ⊆ S)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ U i)
    (hU : ∀ i, PolynomialSignDetermined B (U i)) (z : α → ℝ) :
    PolynomialSignDetermined B (connectedComponentIn S z) := by
  intro x y hxy
  constructor
  · intro hx
    obtain ⟨i,hxi⟩ := hcover x (connectedComponentIn_subset S z hx)
    exact preconnected_cover_member_subset_component hpre hsub hx hxi ((hU i x y hxy).mp hxi)
  · intro hy
    obtain ⟨i,hyi⟩ := hcover y (connectedComponentIn_subset S z hy)
    exact preconnected_cover_member_subset_component hpre hsub hy hyi ((hU i x y hxy).mpr hyi)

/-- One joint polynomial family controls all cover members and therefore all
fiber components. The specialized family is chosen before the seed z. -/
theorem finite_semialgebraic_cover_uniform_component_format
    {ρ κ ι : Type*} [Fintype ι]
    (A : Set ((ρ ⊕ κ) → ℝ)) (G : ι → Set ((ρ ⊕ κ) → ℝ))
    (hG : ∀ i, HasPolynomialSignDescription (G i))
    (hpre : ∀ p i, IsPreconnected (projectionFiber (G i) p))
    (hsub : ∀ p i, projectionFiber (G i) p ⊆ projectionFiber A p)
    (hcover : ∀ p x, x ∈ projectionFiber A p → ∃ i, x ∈ projectionFiber (G i) p) :
    ∃ s d : ℕ, ∀ p : ρ → ℝ, ∃ B : Finset (MvPolynomial κ ℝ),
      B.card ≤ s ∧ (∀ q ∈ B, q.totalDegree ≤ d) ∧
      ∀ z, PolynomialSignDetermined B (connectedComponentIn (projectionFiber A p) z) := by
  classical
  choose F hF using hG
  let B : Finset (MvPolynomial (ρ ⊕ κ) ℝ) := Finset.univ.biUnion F
  have hi (i : ι) : F i ⊆ B := by
    intro q hq
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hq⟩
  refine ⟨B.card,B.sup MvPolynomial.totalDegree,?_⟩
  intro p
  refine ⟨specializePolynomialFamily p B,specializePolynomialFamily_card_le p B,
    specializePolynomialFamily_totalDegree_le p B _ (fun q hq => Finset.le_sup hq),?_⟩
  intro z
  apply polynomialSignDetermined_component_of_preconnected_cover _ _
    (fun i => projectionFiber (G i) p) (hpre p) (hsub p) (hcover p)
  intro i
  exact polynomialSignDetermined_projectionFiber p B (G i)
    (polynomialSignDetermined_mono (hF i) (hi i))

end PaperI
