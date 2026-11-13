import PaperILean.CylindricalEndpointPathFamilies

/-! Finite-chain admissibility is defined before path construction. It does
not assume all fibers connected and does not use a definability assertion
about the connected-fiber locus. Prospective tests: checkpoint_122_pre_strategy. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def orientedChainSectionDomain {ρ κ ι : Type} [Fintype ι]
    (P : Set (ρ → ℝ)) (C : ι → Set ((ρ ⊕ κ) → ℝ))
    (x y : (ρ → ℝ) → κ → ℝ) : Set (ρ → ℝ) :=
  {p | p ∈ P ∧ ∃ c : OrientedBoundedCellChain ι,
    Sum.elim (Sum.elim p (x p)) (y p) ∈ orientedCellChainEligibility C c}

theorem orientedChainSectionDomain_subset {ρ κ ι : Type} [Fintype ι]
    (P : Set (ρ → ℝ)) (C : ι → Set ((ρ ⊕ κ) → ℝ)) (x y : (ρ → ℝ) → κ → ℝ) :
    orientedChainSectionDomain P C x y ⊆ P := fun _ hp => hp.1

theorem orientedChainSectionDomain_definable {ρ κ ι : Type}
    [Finite ρ] [Fintype κ] [Fintype ι]
    (P : Set (ρ → ℝ)) (C : ι → Set ((ρ ⊕ κ) → ℝ)) (x y : (ρ → ℝ) → κ → ℝ)
    (hP : (univ : Set ℝ).Definable Language.ring P)
    (hC : ∀ i, (univ : Set ℝ).Definable Language.ring (C i))
    (hX : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P x))
    (hY : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P y)) :
    (univ : Set ℝ).Definable Language.ring (orientedChainSectionDomain P C x y) := by
  classical
  letI : Fintype ρ := Fintype.ofFinite ρ
  have hencode := cad_selectedGraph_pair
    (cad_selectedGraph_pair (coordinateSectionGraph_definable hP (id : ρ → ρ)) hX) hY
  have h := cad_definable_finite_iUnion (fun c : OrientedBoundedCellChain ι =>
    cad_selectedGraph_preimage hencode (orientedCellChainEligibility_definable C hC c))
  convert h using 1
  ext p
  change (p ∈ P ∧ ∃ c, Sum.elim (Sum.elim p (x p)) (y p) ∈ orientedCellChainEligibility C c) ↔ _
  simp only [mem_iUnion,mem_setOf_eq]
  exact ⟨fun ⟨hp,c,hc⟩ => ⟨c,hp,hc⟩,fun ⟨c,hp,hc⟩ => ⟨hp,c,hc⟩⟩

theorem mem_orientedChainSectionDomain_of_preconnected
    {ρ κ ι : Type} [Fintype ι]
    (P : Set (ρ → ℝ)) (C : ι → Set ((ρ ⊕ κ) → ℝ)) (x y : (ρ → ℝ) → κ → ℝ)
    {p : ρ → ℝ} (hp : p ∈ P) (S : Set (κ → ℝ)) (hS : IsPreconnected S)
    (hCS : ∀ i, projectionFiber (C i) p ⊆ S)
    (hcover : ∀ z ∈ S, ∃ i, z ∈ projectionFiber (C i) p)
    (hx : x p ∈ S) (hy : y p ∈ S) : p ∈ orientedChainSectionDomain P C x y := by
  obtain ⟨c,hc⟩ := connected_finite_cover_has_cellChainEligibility C p S hS hCS hcover
    (x p) (y p) hx hy
  obtain ⟨σ,hσ⟩ := cellChainEligibility_has_orientation C c hc
  exact ⟨hp,⟨c,σ⟩,hσ⟩

end PaperI
