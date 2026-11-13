import PaperILean.CylindricalSliceGraphs

/-! Finite compatible families of half-roof slices extracted from the existing
initial-band CAD input. Leaves are a cover, not an asserted disjoint partition.
The time-independent cylinder is introduced locally; no new contract is used. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable

def cadTimeCylinder {ρ : Type} (n : ℕ) (E : Set (CADVariables ρ n → ℝ)) :
    Set (CADVariables (ρ ⊕ Unit) n → ℝ) := {z | cadDropTime n z ∈ E}

theorem cadTimeCylinder_definable {ρ : Type} (n : ℕ)
    {E : Set (CADVariables ρ n → ℝ)}
    (hE : (univ : Set ℝ).Definable Language.ring E) :
    (univ : Set ℝ).Definable Language.ring (cadTimeCylinder n E) :=
  hE.preimage_comp (cadKeepCoordinate n)

abbrev CylindricalInitialBandDecomposition.slicedLeaf {ρ : Type} {n : ℕ}
    {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) :=
  {ij : (i : Fin d.count) × Fin (d.leafCount i) // d.cell ij.1 ij.2 ⊆ cadTimeCylinder n E}

def CylindricalInitialBandDecomposition.slicedCell {ρ : Type} {n : ℕ}
    {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E))
    (j : d.slicedLeaf) : Set (CADVariables ρ n → ℝ) :=
  cadTowerSlice n (d.base j.val.1) (d.roof j.val.1).value (d.cell j.val.1 j.val.2)

theorem CylindricalInitialBandDecomposition.slicedCell_definable
    {ρ : Type} [Finite ρ] {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) (j : d.slicedLeaf) :
    (univ : Set ℝ).Definable Language.ring (d.slicedCell j) :=
  cadTowerSlice_definable n (d.roof j.val.1).graph_definable
    ((d.tower j.val.1 j.val.2).region_definable (cadInitialBand_definable (d.roof j.val.1).graph_definable))

theorem CylindricalInitialBandDecomposition.slicedCell_subset
    {ρ : Type} {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) (j : d.slicedLeaf) :
    d.slicedCell j ⊆ E := by
  intro z hz
  have h := j.property hz.2
  change cadDropTime n (cadInsertTime n z _) ∈ E at h
  simpa only [cadDropTime_insert] using h

theorem CylindricalInitialBandDecomposition.slicedCell_base
    {ρ : Type} {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) (j : d.slicedLeaf)
    {z : CADVariables ρ n → ℝ} (hz : z ∈ d.slicedCell j) : z ∘ cadBaseCoordinate n ∈ P :=
  d.base_subset j.val.1 hz.1

theorem CylindricalInitialBandDecomposition.slicedCell_cover
    {ρ : Type} {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E))
    {z : CADVariables ρ n → ℝ} (hz : z ∈ E) (hp : z ∘ cadBaseCoordinate n ∈ P) :
    ∃ j : d.slicedLeaf, z ∈ d.slicedCell j := by
  obtain ⟨i,hi⟩ := d.base_cover _ hp
  let w := cadSliceInsert n (d.roof i).value z
  have hw : w ∘ cadBaseCoordinate n ∈ cadInitialBand (d.base i) (d.roof i).value := by
    rw [show w = cadInsertTime n z ((d.roof i).value (z ∘ cadBaseCoordinate n)/2) from rfl,cadInsertTime_base]
    have hpos := d.roof_positive i _ hi
    exact ⟨hi,by dsimp; linarith,by dsimp; linarith⟩
  obtain ⟨j,hj⟩ := d.cover i w hw
  have hE : w ∈ cadTimeCylinder n E := by
    change cadDropTime n (cadInsertTime n z _) ∈ E
    simpa only [cadDropTime_insert] using hz
  rcases d.compatible i j with hsub | hdis
  · exact ⟨⟨⟨i,j⟩,hsub⟩,hi,hj⟩
  · exact (Set.disjoint_left.mp hdis hj hE).elim

theorem CylindricalInitialBandDecomposition.slicedCell_cover_iff
    {ρ : Type} {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) (z : CADVariables ρ n → ℝ) :
    (∃ j : d.slicedLeaf, z ∈ d.slicedCell j) ↔ z ∈ E ∧ z ∘ cadBaseCoordinate n ∈ P :=
  ⟨fun ⟨j,hj⟩ => ⟨d.slicedCell_subset j hj,d.slicedCell_base j hj⟩,
    fun ⟨hz,hp⟩ => d.slicedCell_cover hz hp⟩

theorem CylindricalInitialBandDecomposition.slicedCell_fiber_nonempty
    {ρ : Type} {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) (j : d.slicedLeaf)
    {p : ρ → ℝ} (hp : p ∈ d.base j.val.1) :
    ∃ z ∈ d.slicedCell j, z ∘ cadBaseCoordinate n = p := by
  let c := d.tower j.val.1 j.val.2
  let t := (d.roof j.val.1).value p / 2
  let v := Sum.elim p (fun _ : Unit => t)
  have hv : v ∈ cadInitialBand (d.base j.val.1) (d.roof j.val.1).value := by
    have hpos := d.roof_positive j.val.1 p hp
    exact ⟨hp,by dsimp [v,t]; linarith,by dsimp [v,t]; linarith⟩
  let w := c.sectionMap v
  have hw : w ∘ cadBaseCoordinate n = v := c.sectionMap_projection v
  have hp' : cadDropTime n w ∘ cadBaseCoordinate n = p := by
    rw [cadDropTime_base,hw]; rfl
  refine ⟨cadDropTime n w,⟨hp'.symm ▸ hp,?_⟩,hp'⟩
  change cadInsertTime n (cadDropTime n w) ((d.roof j.val.1).value (cadDropTime n w ∘ cadBaseCoordinate n)/2) ∈ _
  rw [hp']
  have ht : w (cadBaseCoordinate n (Sum.inr ())) = (d.roof j.val.1).value p/2 := congrFun hw (Sum.inr ())
  rw [← ht,cadInsertTime_drop]
  exact c.sectionMap_mem hv

theorem published_cylindrical_timeCylinder_decomposition
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ) (P : Set (ρ → ℝ)) (E : Set (CADVariables ρ n → ℝ))
    (hP : HasPolynomialSignDescription P) (hE : HasPolynomialSignDescription E) :
    Nonempty (CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) :=
  hCAD.decomposition n P (cadTimeCylinder n E) hP
    (hQE.finite_sign_description _ (cadTimeCylinder_definable n (hasPolynomialSignDescription_definable hE)))

end PaperI
