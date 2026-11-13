import PaperILean.HardtTransportedComponents
import PaperILean.UniformComponentSignFormat
import Mathlib.Data.Fintype.EquivFin

/-! A joint finite partition into actual fiber components. This is constructed
from the existing accepted cell, compatible Hardt, and real-QE inputs. -/

noncomputable section
namespace PaperI
open Set

structure JointComponentPartition {ρ κ : Type*} (A : Set ((ρ ⊕ κ) → ℝ)) where
  count : ℕ
  part : Fin count → Set ((ρ ⊕ κ) → ℝ)
  semialgebraic : ∀ i, HasPolynomialSignDescription (part i)
  subset : ∀ p i, projectionFiber (part i) p ⊆ projectionFiber A p
  cover : ∀ p x, x ∈ projectionFiber A p → ∃ i, x ∈ projectionFiber (part i) p
  component : ∀ p i x, x ∈ projectionFiber (part i) p →
    projectionFiber (part i) p = connectedComponentIn (projectionFiber A p) x
  disjoint : ∀ p, Pairwise (fun i j =>
    Disjoint (projectionFiber (part i) p) (projectionFiber (part j) p))

theorem published_joint_component_partition
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Finite κ]
    (A : Set ((ρ ⊕ κ) → ℝ)) (hA : HasPolynomialSignDescription A) :
    Nonempty (JointComponentPartition A) := by
  classical
  have hdom := published_real_projection_has_sign_description hQE
    (hasPolynomialSignDescription_definable hA)
  obtain ⟨D⟩ := hHardt.projection_trivialization A (fun _ => A) hA hdom
    (fun _ => hA) (fun _ => subset_rfl)
  obtain ⟨s,d,hComp⟩ := published_family_uniform_component_sign_format hCell hHardt hQE A hA
  letI : ∀ i : Fin D.n, Finite (ConnectedComponents (projectionFiber A (D.basePoint i).val)) :=
    fun i => published_finite_connectedComponents hCell.toFiniteConnectedCover _ (D.fiber_semialgebraic i)
  let J := Σ i : Fin D.n, ConnectedComponents (projectionFiber A (D.basePoint i).val)
  letI : Fintype J := Fintype.ofFinite J
  let e := (Fintype.equivFin J).symm
  let G : J → Set ((ρ ⊕ κ) → ℝ) := fun j =>
    hardtTransportSet D.toProjectionHardtData j.1
      (componentSet (projectionFiber A (D.basePoint j.1).val) j.2)
  have hG (j : J) : HasPolynomialSignDescription (G j) := by
    obtain ⟨B,_,_,hB⟩ := hComp (D.basePoint j.1).val
    apply hQE.finite_sign_description
    apply hardtTransportSet_definable D
    rw [componentSet_eq_connectedComponentIn]
    exact ⟨B,hB _⟩
  refine ⟨{
    count := Fintype.card J
    part := fun i => G (e i)
    semialgebraic := fun i => hG (e i)
    subset := fun p i => hardtTransportSet_fiber_subset D.toProjectionHardtData _ _ p
    cover := ?_
    component := ?_
    disjoint := ?_ }⟩
  · intro p x hx
    obtain ⟨i,c,hc⟩ := hardtTransportSet_component_cover D.toProjectionHardtData p hx
    refine ⟨e.symm ⟨i,c⟩,?_⟩
    simpa only [Equiv.apply_symm_apply] using hc
  · intro p i x hx
    have hp : p ∈ D.piece (e i).1 := hx.choose_spec.2.1
    change projectionFiber (hardtTransportSet D.toProjectionHardtData (e i).1
      (componentSet _ (e i).2)) p = _
    rw [hardtTransportSet_component_fiber D.toProjectionHardtData (e i).1 ⟨p,hp⟩]
    apply componentSet_eq_of_mem
    rwa [hardtTransportSet_component_fiber D.toProjectionHardtData (e i).1 ⟨p,hp⟩] at hx
  · intro p i j hij
    exact hardtTransportSet_component_pairwiseDisjoint D.toProjectionHardtData p
      (fun h => hij (e.injective h))

namespace JointComponentPartition
variable {ρ κ : Type*} {A : Set ((ρ ⊕ κ) → ℝ)} (D : JointComponentPartition A)

def activeComponentMap (p : ρ → ℝ)
    (i : {i : Fin D.count // (projectionFiber (D.part i) p).Nonempty}) :
    ConnectedComponents (projectionFiber A p) :=
  ConnectedComponents.mk ⟨i.property.choose,D.subset p i.val i.property.choose_spec⟩

theorem activeComponentMap_fiber (p : ρ → ℝ)
    (i : {i : Fin D.count // (projectionFiber (D.part i) p).Nonempty}) :
    componentSet (projectionFiber A p) (D.activeComponentMap p i) =
      projectionFiber (D.part i.val) p := by
  rw [componentSet_eq_of_mem _ _
    (show i.property.choose ∈ componentSet (projectionFiber A p) (D.activeComponentMap p i)
      from ⟨D.subset p i.val i.property.choose_spec,rfl⟩)]
  exact (D.component p i.val _ i.property.choose_spec).symm

theorem activeComponentMap_injective (p : ρ → ℝ) :
    Function.Injective (D.activeComponentMap p) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have heq : projectionFiber (D.part i.val) p = projectionFiber (D.part j.val) p := by
    rw [← D.activeComponentMap_fiber p i,← D.activeComponentMap_fiber p j,hij]
  exact (disjoint_left.mp (D.disjoint p hne)) i.property.choose_spec
    (heq ▸ i.property.choose_spec)

theorem activeComponentMap_surjective (p : ρ → ℝ) :
    Function.Surjective (D.activeComponentMap p) := by
  intro c
  let x := componentPoint c
  obtain ⟨i,hi⟩ := D.cover p x.val x.property
  let j : {i : Fin D.count // (projectionFiber (D.part i) p).Nonempty} := ⟨i,x.val,hi⟩
  refine ⟨j,?_⟩
  have hx : x.val ∈ componentSet (projectionFiber A p) (D.activeComponentMap p j) := by
    rw [D.activeComponentMap_fiber]
    exact hi
  obtain ⟨_,hx⟩ := hx
  exact hx.symm.trans (componentPoint_spec c)

include D in
theorem finite_components (p : ρ → ℝ) : Finite (ConnectedComponents (projectionFiber A p)) :=
  Finite.of_surjective (D.activeComponentMap p) (D.activeComponentMap_surjective p)

theorem active_count_eq_components (p : ρ → ℝ) :
    Nat.card {i : Fin D.count // (projectionFiber (D.part i) p).Nonempty} =
      Nat.card (ConnectedComponents (projectionFiber A p)) :=
  Nat.card_congr (Equiv.ofBijective (D.activeComponentMap p)
    ⟨D.activeComponentMap_injective p,D.activeComponentMap_surjective p⟩)

theorem component_count_le (p : ρ → ℝ) :
    Nat.card (ConnectedComponents (projectionFiber A p)) ≤ D.count := by
  rw [← D.active_count_eq_components]
  exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans_eq
    (by simp)

theorem part_eq_component_of_mem (p : ρ → ℝ) (i : Fin D.count) {x : κ → ℝ}
    (hx : x ∈ projectionFiber (D.part i) p) :
    projectionFiber (D.part i) p = connectedComponentIn (projectionFiber A p) x :=
  D.component p i x hx

end JointComponentPartition
end PaperI
