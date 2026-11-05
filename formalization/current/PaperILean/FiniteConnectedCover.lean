import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-! Local counting infrastructure for I633 and I638. A finite preconnected
cover supplies actual finiteness of the component quotient before its natural
cardinality is used. Empty pieces and empty spaces are allowed. These results
do not assert existence of a cell decomposition or a format-uniform bound. -/

noncomputable section
namespace PaperI
open Set Function

/-- Choose one component from each nonempty cover piece. -/
def preconnectedCoverComponent {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) : {i : ι // (U i).Nonempty} → ConnectedComponents X :=
  fun i => ConnectedComponents.mk i.property.choose

theorem preconnectedCoverComponent_surjective {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (hpre : ∀ i, IsPreconnected (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) : Surjective (preconnectedCoverComponent U) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨i, hxi⟩ := hcover x
  let j : {i : ι // (U i).Nonempty} := ⟨i, x, hxi⟩
  refine ⟨j, ?_⟩
  apply ConnectedComponents.coe_eq_coe'.mpr
  exact (hpre i).subset_connectedComponent hxi j.property.choose_spec

theorem finite_connectedComponents_of_finite_preconnected_cover
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (U : ι → Set X) (hpre : ∀ i, IsPreconnected (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) : Finite (ConnectedComponents X) :=
  Finite.of_surjective (preconnectedCoverComponent U)
    (preconnectedCoverComponent_surjective U hpre hcover)

theorem card_connectedComponents_le_of_finite_preconnected_cover
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (U : ι → Set X) (hpre : ∀ i, IsPreconnected (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) : Nat.card (ConnectedComponents X) ≤ Nat.card ι := by
  letI : Finite (ConnectedComponents X) :=
    finite_connectedComponents_of_finite_preconnected_cover U hpre hcover
  exact (Nat.card_le_card_of_surjective (preconnectedCoverComponent U)
    (preconnectedCoverComponent_surjective U hpre hcover)).trans
      (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

theorem finite_connectedComponents_and_card_le_of_finite_preconnected_cover
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (U : ι → Set X) (hpre : ∀ i, IsPreconnected (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    Finite (ConnectedComponents X) ∧ Nat.card (ConnectedComponents X) ≤ Nat.card ι :=
  ⟨finite_connectedComponents_of_finite_preconnected_cover U hpre hcover,
    card_connectedComponents_le_of_finite_preconnected_cover U hpre hcover⟩

/-- A homeomorphism induces a bijection of actual connected components. -/
def connectedComponentsEquivOfHomeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := e.continuous.connectedComponentsMap
  invFun := e.symm.continuous.connectedComponentsMap
  left_inv c := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    change ConnectedComponents.mk (e.symm (e x)) = ConnectedComponents.mk x
    rw [e.symm_apply_apply]
  right_inv c := by
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    change ConnectedComponents.mk (e (e.symm y)) = ConnectedComponents.mk y
    rw [e.apply_symm_apply]

theorem finite_connectedComponents_of_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    [Finite (ConnectedComponents X)] : Finite (ConnectedComponents Y) :=
  Finite.of_equiv _ (connectedComponentsEquivOfHomeomorph e)

theorem card_connectedComponents_eq_of_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Nat.card (ConnectedComponents X) = Nat.card (ConnectedComponents Y) :=
  Nat.card_congr (connectedComponentsEquivOfHomeomorph e)

theorem finite_connectedComponents_and_card_le_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {N : ℕ} (h : Finite (ConnectedComponents X) ∧
      Nat.card (ConnectedComponents X) ≤ N) :
    Finite (ConnectedComponents Y) ∧ Nat.card (ConnectedComponents Y) ≤ N := by
  letI : Finite (ConnectedComponents X) := h.1
  exact ⟨finite_connectedComponents_of_homeomorph e,
    (card_connectedComponents_eq_of_homeomorph e).symm.trans_le h.2⟩

/-- For a totally disconnected space each component contains exactly one point.
This is not an assertion about any semialgebraic dimension definition. -/
def equivConnectedComponentsOfTotallyDisconnected {X : Type*}
    [TopologicalSpace X] [TotallyDisconnectedSpace X] : X ≃ ConnectedComponents X :=
  Equiv.ofBijective ConnectedComponents.mk ⟨by
    intro x y h
    have hx := ConnectedComponents.coe_eq_coe'.mp h
    simpa only [connectedComponent_eq_singleton, mem_singleton_iff] using hx,
    ConnectedComponents.surjective_coe⟩

theorem finite_of_finite_connectedComponents_of_totallyDisconnected {X : Type*}
    [TopologicalSpace X] [TotallyDisconnectedSpace X]
    [Finite (ConnectedComponents X)] : Finite X :=
  Finite.of_equiv _ equivConnectedComponentsOfTotallyDisconnected.symm

theorem card_eq_connectedComponents_of_totallyDisconnected {X : Type*}
    [TopologicalSpace X] [TotallyDisconnectedSpace X] :
    Nat.card X = Nat.card (ConnectedComponents X) :=
  Nat.card_congr equivConnectedComponentsOfTotallyDisconnected

theorem finite_and_card_le_of_totallyDisconnected {X : Type*}
    [TopologicalSpace X] [TotallyDisconnectedSpace X] {N : ℕ}
    (h : Finite (ConnectedComponents X) ∧ Nat.card (ConnectedComponents X) ≤ N) :
    Finite X ∧ Nat.card X ≤ N := by
  letI : Finite (ConnectedComponents X) := h.1
  exact ⟨finite_of_finite_connectedComponents_of_totallyDisconnected,
    card_eq_connectedComponents_of_totallyDisconnected.trans_le h.2⟩

end PaperI
