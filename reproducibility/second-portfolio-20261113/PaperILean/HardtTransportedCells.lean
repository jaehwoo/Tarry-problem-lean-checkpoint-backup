import PaperILean.ConnectedCoverSignFormat
import PaperILean.PublishedSemialgebraicPaths
import PaperILean.PublishedSemialgebraicCellDecomposition

/-! Transport actual semialgebraic cover members through the recorded Hardt
chart graph. Empty fibers outside each chart piece remain empty. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def hardtTransportSet {ρ κ : Type*} {A : Set ((ρ ⊕ κ) → ℝ)}
    (D : ProjectionHardtData A) (i : Fin D.n) (S : Set (κ → ℝ)) :
    Set ((ρ ⊕ κ) → ℝ) :=
  {v | ∃ x : κ → ℝ, x ∈ S ∧
    Sum.elim (Sum.elim (fun r => v (Sum.inl r)) x)
      (fun k => v (Sum.inr k)) ∈ D.chartGraph i}

theorem hardtTransportSet_definable {ρ κ : Type*} [Finite ρ] [Finite κ]
    {A : Set ((ρ ⊕ κ) → ℝ)} {mark : Fin 2 → Set ((ρ ⊕ κ) → ℝ)}
    (D : CompatibleProjectionHardtData A mark) (i : Fin D.n)
    {S : Set (κ → ℝ)} (hS : HasPolynomialSignDescription S) :
    (univ : Set ℝ).Definable Language.ring (hardtTransportSet D.toProjectionHardtData i S) := by
  let e : (ρ ⊕ κ) ⊕ κ → (ρ ⊕ κ) ⊕ κ :=
    Sum.elim (Sum.elim (fun r => Sum.inl (Sum.inl r)) Sum.inr)
      (fun k => Sum.inl (Sum.inr k))
  have h := realDefinable_exists
    (((hasPolynomialSignDescription_definable hS).preimage_comp
      (Sum.inr : κ → (ρ ⊕ κ) ⊕ κ)).inter
      ((hasPolynomialSignDescription_definable (D.chart_semialgebraic i)).preimage_comp e))
  exact h

theorem hardtTransportSet_fiber_eq_range {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (p : D.piece i) (S : Set (κ → ℝ))
    (hS : S ⊆ projectionFiber A (D.basePoint i).val) :
    projectionFiber (hardtTransportSet D i S) p.val =
      range (fun x : S => (D.fiberHomeomorph i p ⟨x.val,hS x.property⟩).val) := by
  ext y
  constructor
  · rintro ⟨x,hx,hp,hf,hy⟩
    exact ⟨⟨x,hx⟩,hy.symm⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x.val,x.property,p.property,hS x.property,rfl⟩

theorem hardtTransportSet_fiber_empty {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (S : Set (κ → ℝ)) {p : ρ → ℝ}
    (hp : p ∉ D.piece i) : projectionFiber (hardtTransportSet D i S) p = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  rintro y ⟨x,hx,hpi,hf,hy⟩
  exact hp hpi

theorem hardtTransportSet_fiber_subset {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (S : Set (κ → ℝ)) (p : ρ → ℝ) :
    projectionFiber (hardtTransportSet D i S) p ⊆ projectionFiber A p := by
  rintro y ⟨x,hx,hp,hf,hy⟩
  change y = (D.chart i (⟨p,hp⟩,⟨x,hf⟩)).val.2 at hy
  rw [hy]
  exact (D.fiberHomeomorph i ⟨p,hp⟩ ⟨x,hf⟩).property

theorem hardtTransportSet_fiber_preconnected {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (S : Set (κ → ℝ))
    (hS : S ⊆ projectionFiber A (D.basePoint i).val)
    (hc : IsPreconnected S) (p : ρ → ℝ) :
    IsPreconnected (projectionFiber (hardtTransportSet D i S) p) := by
  by_cases hp : p ∈ D.piece i
  · rw [hardtTransportSet_fiber_eq_range D i ⟨p,hp⟩ S hS]
    letI : PreconnectedSpace S := Subtype.preconnectedSpace hc
    apply isPreconnected_range
    exact continuous_subtype_val.comp ((D.fiberHomeomorph i ⟨p,hp⟩).continuous.comp
      (continuous_subtype_val.subtype_mk (fun x => hS x.property)))
  · rw [hardtTransportSet_fiber_empty D i S hp]
    exact isPreconnected_empty

theorem SemialgebraicCellDecomposition.cell_isPreconnected {κ : Type*}
    {S : Set (κ → ℝ)} (c : SemialgebraicCellDecomposition S) (i : Fin c.count) :
    IsPreconnected (c.cell i) := by
  letI : PreconnectedSpace (openUnitCube (c.dimension i)) :=
    Subtype.preconnectedSpace (openUnitCube_isPreconnected _)
  have h := isPreconnected_range (continuous_subtype_val.comp (c.chart i).continuous)
  have heq : range (fun x => (c.chart i x).val) = c.cell i := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact (c.chart i y).property
    · intro hx
      refine ⟨(c.chart i).symm ⟨x,hx⟩,?_⟩
      simp only [Homeomorph.apply_symm_apply]
  change IsPreconnected (range (fun x => (c.chart i x).val)) at h
  rwa [heq] at h

theorem hardtTransportSet_cell_cover {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (c : ∀ i : Fin D.n, SemialgebraicCellDecomposition (projectionFiber A (D.basePoint i).val))
    (p : ρ → ℝ) (x : κ → ℝ) (hx : x ∈ projectionFiber A p) :
    ∃ i : Fin D.n, ∃ j : Fin (c i).count,
      x ∈ projectionFiber (hardtTransportSet D i ((c i).cell j)) p := by
  obtain ⟨i,hp⟩ := D.cover p ⟨x,hx⟩
  let y := (D.fiberHomeomorph i ⟨p,hp⟩).symm ⟨x,hx⟩
  obtain ⟨j,hj⟩ := (c i).cover y.val y.property
  refine ⟨i,j,y.val,hj,hp,y.property,?_⟩
  change x = ((D.fiberHomeomorph i ⟨p,hp⟩)
    ((D.fiberHomeomorph i ⟨p,hp⟩).symm ⟨x,hx⟩)).val
  simp only [Homeomorph.apply_symm_apply]

end PaperI
