import PaperILean.HardtTransportedCells
import PaperILean.FiniteConnectedCover

/-! Original I1259/I1265: transport whole connected components, not cells.
Reference representatives are chosen once, before the varying parameter. -/

noncomputable section
namespace PaperI
open Set

def componentPoint {X : Type*} [TopologicalSpace X]
    (c : ConnectedComponents X) : X :=
  Classical.choose (ConnectedComponents.surjective_coe c)

theorem componentPoint_spec {X : Type*} [TopologicalSpace X]
    (c : ConnectedComponents X) : ConnectedComponents.mk (componentPoint c) = c :=
  Classical.choose_spec (ConnectedComponents.surjective_coe c)

def componentSet {X : Type*} [TopologicalSpace X] (S : Set X)
    (c : ConnectedComponents S) : Set X :=
  {x | ∃ hx : x ∈ S, ConnectedComponents.mk (⟨x,hx⟩ : S) = c}

theorem componentSet_subset {X : Type*} [TopologicalSpace X] (S : Set X)
    (c : ConnectedComponents S) : componentSet S c ⊆ S :=
  fun _ h => h.choose

theorem componentSet_nonempty {X : Type*} [TopologicalSpace X] (S : Set X)
    (c : ConnectedComponents S) : (componentSet S c).Nonempty :=
  ⟨(componentPoint c).val, (componentPoint c).property, componentPoint_spec c⟩

theorem componentSet_eq_connectedComponentIn {X : Type*} [TopologicalSpace X]
    (S : Set X) (c : ConnectedComponents S) :
    componentSet S c = connectedComponentIn S (componentPoint c).val := by
  rw [connectedComponentIn_eq_image (componentPoint c).property]
  ext x
  constructor
  · rintro ⟨hx,hc⟩
    exact ⟨⟨x,hx⟩,ConnectedComponents.coe_eq_coe'.mp
      (hc.trans (componentPoint_spec c).symm),rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,(ConnectedComponents.coe_eq_coe'.mpr hy).trans (componentPoint_spec c)⟩

theorem componentSet_eq_of_mem {X : Type*} [TopologicalSpace X]
    (S : Set X) (c : ConnectedComponents S) {x : X} (hx : x ∈ componentSet S c) :
    componentSet S c = connectedComponentIn S x := by
  rw [componentSet_eq_connectedComponentIn] at hx ⊢
  exact connectedComponentIn_eq hx

theorem componentSet_pairwiseDisjoint {X : Type*} [TopologicalSpace X] (S : Set X) :
    Pairwise (fun c d : ConnectedComponents S => Disjoint (componentSet S c) (componentSet S d)) := by
  intro c d hcd
  rw [disjoint_left]
  rintro x ⟨hx,hc⟩ ⟨_,hd⟩
  exact hcd (hc.symm.trans hd)

theorem componentSet_cover {X : Type*} [TopologicalSpace X] (S : Set X)
    {x : X} (hx : x ∈ S) : ∃ c, x ∈ componentSet S c :=
  ⟨ConnectedComponents.mk (⟨x,hx⟩ : S),hx,rfl⟩

theorem hardtTransportSet_component_fiber {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (p : D.piece i)
    (c : ConnectedComponents (projectionFiber A (D.basePoint i).val)) :
    projectionFiber (hardtTransportSet D i
      (componentSet (projectionFiber A (D.basePoint i).val) c)) p.val =
      componentSet (projectionFiber A p.val)
        (connectedComponentsEquivOfHomeomorph (D.fiberHomeomorph i p) c) := by
  let e := D.fiberHomeomorph i p
  let ce := connectedComponentsEquivOfHomeomorph e
  ext y
  constructor
  · rintro ⟨x,⟨hx,hc⟩,hp,hf,hy⟩
    have hy' : y = (e ⟨x,hx⟩).val := hy
    subst y
    refine ⟨(e ⟨x,hx⟩).property,?_⟩
    change ce (ConnectedComponents.mk (⟨x,hx⟩ : projectionFiber A (D.basePoint i).val)) = ce c
    exact congrArg ce hc
  · rintro ⟨hy,hc⟩
    let x := e.symm ⟨y,hy⟩
    have hx : ConnectedComponents.mk x = c := by
      apply ce.injective
      change ConnectedComponents.mk (e (e.symm ⟨y,hy⟩)) = ce c
      simpa only [Homeomorph.apply_symm_apply] using hc
    refine ⟨x.val,⟨x.property,hx⟩,p.property,x.property,?_⟩
    change y = (e (e.symm ⟨y,hy⟩)).val
    rw [Homeomorph.apply_symm_apply]

theorem hardtTransportSet_component_cover {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (p : ρ → ℝ) {x : κ → ℝ} (hx : x ∈ projectionFiber A p) :
    ∃ i : Fin D.n, ∃ c : ConnectedComponents (projectionFiber A (D.basePoint i).val),
      x ∈ projectionFiber (hardtTransportSet D i
        (componentSet (projectionFiber A (D.basePoint i).val) c)) p := by
  obtain ⟨i,hp⟩ := D.cover p ⟨x,hx⟩
  let e := D.fiberHomeomorph i ⟨p,hp⟩
  let y := e.symm ⟨x,hx⟩
  refine ⟨i,ConnectedComponents.mk y,y.val,⟨y.property,rfl⟩,hp,y.property,?_⟩
  change x = (e (e.symm ⟨x,hx⟩)).val
  rw [Homeomorph.apply_symm_apply]

theorem hardtTransportSet_component_pairwiseDisjoint {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A) (p : ρ → ℝ) :
    Pairwise (fun j k : (Σ i : Fin D.n, ConnectedComponents (projectionFiber A (D.basePoint i).val)) =>
      Disjoint
        (projectionFiber (hardtTransportSet D j.1
          (componentSet (projectionFiber A (D.basePoint j.1).val) j.2)) p)
        (projectionFiber (hardtTransportSet D k.1
          (componentSet (projectionFiber A (D.basePoint k.1).val) k.2)) p)) := by
  rintro ⟨i,c⟩ ⟨j,d⟩ hne
  rw [disjoint_left]
  intro x hx hy
  have hpi : p ∈ D.piece i := hx.choose_spec.2.1
  have hpj : p ∈ D.piece j := hy.choose_spec.2.1
  have hij : i = j := by
    by_contra h
    exact (disjoint_left.mp (D.disjoint h)) hpi hpj
  subst j
  rw [hardtTransportSet_component_fiber D i ⟨p,hpi⟩] at hx hy
  obtain ⟨hxc,hc⟩ := hx
  obtain ⟨hxd,hd⟩ := hy
  have hcd : c = d := (connectedComponentsEquivOfHomeomorph (D.fiberHomeomorph i ⟨p,hpi⟩)).injective
    (hc.symm.trans hd)
  subst d
  exact hne rfl

end PaperI
