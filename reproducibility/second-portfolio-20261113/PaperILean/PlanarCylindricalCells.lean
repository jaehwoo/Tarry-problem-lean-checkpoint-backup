import PaperILean.PlanarSlicedCellGeometry

/-! I1317: planar cells without boundedness or empty-interior restrictions.
The existing coordinate order is retained: coordinate 1 is lifted first.
Semialgebraicity is supplied separately by the actual joint cell relation. -/
noncomputable section
namespace PaperI
open Set

def IsScalarCylindricalCell (B : Set ℝ) : Prop :=
  (∃ a, B = {a}) ∨ (∃ a b, a < b ∧ B = Ioo a b) ∨
    (∃ a, B = Ioi a) ∨ (∃ b, B = Iio b) ∨ B = univ

def IsPlanarCylindricalCell (S : Set (Fin 2 → ℝ)) : Prop :=
  ∃ B : Set ℝ, IsScalarCylindricalCell B ∧
    ((∃ f : ℝ → ℝ, ContinuousOn f B ∧ S = {x | x 1 ∈ B ∧ x 0 = f (x 1)}) ∨
     (∃ l u : ℝ → ℝ, ContinuousOn l B ∧ ContinuousOn u B ∧
       (∀ t ∈ B, l t < u t) ∧ S = {x | x 1 ∈ B ∧ l (x 1) < x 0 ∧ x 0 < u (x 1)}) ∨
     (∃ l : ℝ → ℝ, ContinuousOn l B ∧ S = {x | x 1 ∈ B ∧ l (x 1) < x 0}) ∨
     (∃ u : ℝ → ℝ, ContinuousOn u B ∧ S = {x | x 1 ∈ B ∧ x 0 < u (x 1)}) ∨
     S = {x | x 1 ∈ B})

theorem CylindricalLift.scalarFiber_isScalarCylindricalCell {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) {p : α → ℝ} (hp : p ∈ U) :
    IsScalarCylindricalCell (c.scalarFiber p) := by
  rcases c.scalarFiber_cases hp with ⟨a,_,ha⟩ | h | h | h | h
  · exact Or.inl ⟨a,ha⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem CylindricalLift.planarFiber_isPlanarCylindricalCell {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) (d : CylindricalLift c.region)
    {p : α → ℝ} (hp : p ∈ U) : IsPlanarCylindricalCell (c.planarFiber d p) := by
  refine ⟨c.scalarFiber p,c.scalarFiber_isScalarCylindricalCell hp,?_⟩
  cases d with
  | graph f =>
    exact Or.inl ⟨_,f.continuousOn_scalarFiber c p,rfl⟩
  | between l u h =>
    exact Or.inr (Or.inl ⟨_,_,l.continuousOn_scalarFiber c p,
      u.continuousOn_scalarFiber c p,fun t ht => h _ ht,rfl⟩)
  | above l =>
    exact Or.inr (Or.inr (Or.inl ⟨_,l.continuousOn_scalarFiber c p,rfl⟩))
  | below u =>
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_,u.continuousOn_scalarFiber c p,rfl⟩)))
  | whole =>
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    ext x
    change (x 1 ∈ c.scalarFiber p ∧ True) ↔ x 1 ∈ c.scalarFiber p
    simp

theorem CylindricalTower.planar_fiber_isPlanarCylindricalCell {α : Type}
    {U : Set (α → ℝ)} {S : Set (CADVariables α 2 → ℝ)}
    (c : CylindricalTower U S) {p : α → ℝ} (hp : p ∈ U) :
    IsPlanarCylindricalCell {x : Fin 2 → ℝ | cadPack 2 p x ∈ S} := by
  cases c with
  | step previous d _ =>
    cases previous with
    | step previous c _ =>
      cases previous
      exact c.planarFiber_isPlanarCylindricalCell d hp

theorem CylindricalInitialBandDecomposition.planar_slicedFiberCell_cases
    {ρ : Type} {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ 2 → ℝ)}
    (d : CylindricalInitialBandDecomposition 2 T (cadTimeCylinder 2 E)) (j : d.slicedLeaf)
    (p : ρ → ℝ) : projectionFiber (d.slicedFiberCell j) p = ∅ ∨
      IsPlanarCylindricalCell (projectionFiber (d.slicedFiberCell j) p) := by
  by_cases hp : p ∈ d.base j.val.1
  · right
    have hpos := d.roof_positive j.val.1 p hp
    have hv : Sum.elim p (fun _ : Unit => (d.roof j.val.1).value p / 2) ∈
        cadInitialBand (d.base j.val.1) (d.roof j.val.1).value :=
      ⟨hp,by dsimp; linarith,by dsimp; linarith⟩
    rw [d.planar_slicedFiberCell_eq_tower_fiber j hp]
    exact (d.tower j.val.1 j.val.2).planar_fiber_isPlanarCylindricalCell hv
  · exact Or.inl (d.slicedFiberCell_eq_empty_of_not_mem_base j hp)

end PaperI
