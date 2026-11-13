import PaperILean.PlanarCylindricalCellGeometry
import PaperILean.CylindricalJointConnectedPaths

/-! I1261: apply the two-lift classification to actual half-roof CAD slices.
Inactive parameter cells give empty fibers. No dimension conclusion or graph
cover is supplied as an external assumption. -/
noncomputable section
namespace PaperI
open Set

theorem CylindricalTower.bounded_thin_planar_fiber_cases {α : Type}
    {U : Set (α → ℝ)} {S : Set (CADVariables α 2 → ℝ)}
    (c : CylindricalTower U S) {p : α → ℝ} (hp : p ∈ U)
    (hthin : interior {x : Fin 2 → ℝ | cadPack 2 p x ∈ S} = ∅)
    (hlo : ∀ i : Fin 2, BddBelow ((fun x => x i) '' {x | cadPack 2 p x ∈ S}))
    (hhi : ∀ i : Fin 2, BddAbove ((fun x => x i) '' {x | cadPack 2 p x ∈ S})) :
    (∃ z, {x : Fin 2 → ℝ | cadPack 2 p x ∈ S} = {z}) ∨
      IsPlanarIntervalGraph {x : Fin 2 → ℝ | cadPack 2 p x ∈ S} := by
  cases c with
  | step previous d _ =>
    cases previous with
    | step previous c _ =>
      cases previous
      exact c.bounded_thin_planarFiber_cases d hp hthin hlo hhi

theorem cadInsertTime_pack_two {ρ : Type} (p : ρ → ℝ) (x : Fin 2 → ℝ) (t : ℝ) :
    cadInsertTime 2 (cadPack 2 p x) t = cadPack 2 (Sum.elim p (fun _ : Unit => t)) x := rfl

theorem CylindricalInitialBandDecomposition.planar_slicedFiberCell_eq_tower_fiber
    {ρ : Type} {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ 2 → ℝ)}
    (d : CylindricalInitialBandDecomposition 2 T (cadTimeCylinder 2 E)) (j : d.slicedLeaf)
    {p : ρ → ℝ} (hp : p ∈ d.base j.val.1) :
    projectionFiber (d.slicedFiberCell j) p =
      {x : Fin 2 → ℝ | cadPack 2 (Sum.elim p (fun _ : Unit => (d.roof j.val.1).value p / 2)) x ∈
        d.cell j.val.1 j.val.2} := by
  ext x
  change (cadPack 2 p x ∘ cadBaseCoordinate 2 ∈ d.base j.val.1 ∧
    cadInsertTime 2 (cadPack 2 p x)
      ((d.roof j.val.1).value (cadPack 2 p x ∘ cadBaseCoordinate 2) / 2) ∈ _) ↔ _
  rw [cadPack_base, cadInsertTime_pack_two]
  exact and_iff_right hp

theorem CylindricalInitialBandDecomposition.slicedFiberCell_eq_empty_of_not_mem_base
    {ρ : Type} {n : ℕ} {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E)) (j : d.slicedLeaf)
    {p : ρ → ℝ} (hp : p ∉ d.base j.val.1) :
    projectionFiber (d.slicedFiberCell j) p = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  intro x hx
  have h : cadPack n p x ∘ cadBaseCoordinate n ∈ d.base j.val.1 := hx.1
  exact hp (by simpa only [cadPack_base] using h)

/-- A case split for each actual leaf, including inactive leaves. Boundedness
and empty interior refer to the unchanged planar fiber. -/
theorem CylindricalInitialBandDecomposition.bounded_thin_planar_slicedFiberCell_cases
    {ρ : Type} {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ 2 → ℝ)}
    (d : CylindricalInitialBandDecomposition 2 T (cadTimeCylinder 2 E)) (j : d.slicedLeaf)
    (p : ρ → ℝ) (hthin : interior (projectionFiber (d.slicedFiberCell j) p) = ∅)
    (hlo : ∀ i : Fin 2, BddBelow ((fun x => x i) '' projectionFiber (d.slicedFiberCell j) p))
    (hhi : ∀ i : Fin 2, BddAbove ((fun x => x i) '' projectionFiber (d.slicedFiberCell j) p)) :
    projectionFiber (d.slicedFiberCell j) p = ∅ ∨
      (∃ z, projectionFiber (d.slicedFiberCell j) p = {z}) ∨
      IsPlanarIntervalGraph (projectionFiber (d.slicedFiberCell j) p) := by
  by_cases hp : p ∈ d.base j.val.1
  · right
    have hpos := d.roof_positive j.val.1 p hp
    have hv : Sum.elim p (fun _ : Unit => (d.roof j.val.1).value p / 2) ∈
        cadInitialBand (d.base j.val.1) (d.roof j.val.1).value :=
      ⟨hp, by dsimp; linarith, by dsimp; linarith⟩
    have he := d.planar_slicedFiberCell_eq_tower_fiber j hp
    rw [he] at hthin hlo hhi ⊢
    exact (d.tower j.val.1 j.val.2).bounded_thin_planar_fiber_cases hv hthin hlo hhi
  · exact Or.inl (d.slicedFiberCell_eq_empty_of_not_mem_base j hp)

end PaperI
