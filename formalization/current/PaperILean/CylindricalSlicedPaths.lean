import PaperILean.CylindricalSliceCoordinates

/-! A tower over an initial band gives actual paths in each half-roof slice.
The auxiliary base time is preserved by the tower path, not estimated below
by a uniform constant. This file adds no published assumption. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def cadSliceInsert {ρ : Type} (n : ℕ) (β : (ρ → ℝ) → ℝ)
    (z : CADVariables ρ n → ℝ) : CADVariables (ρ ⊕ Unit) n → ℝ :=
  cadInsertTime n z (β (z ∘ cadBaseCoordinate n) / 2)

def cadTowerSlice {ρ : Type} (n : ℕ) (P : Set (ρ → ℝ)) (β : (ρ → ℝ) → ℝ)
    (S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)) : Set (CADVariables ρ n → ℝ) :=
  {z | z ∘ cadBaseCoordinate n ∈ P ∧ cadSliceInsert n β z ∈ S}

theorem cadSliceInsert_selectedGraph {α ρ : Type} [Finite α] [Finite ρ]
    {D : Set (α → ℝ)} {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    (n : ℕ) {z : (α → ℝ) → CADVariables ρ n → ℝ}
    (hz : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D z))
    (hβ : CADScalarDefinable P β)
    (hmap : MapsTo (fun p => z p ∘ cadBaseCoordinate n) D P) :
    (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph D (fun p => cadSliceInsert n β (z p))) := by
  have hD := selectedFunctionGraph_domain_definable D z hz
  have h : CADScalarDefinable D (fun p => β (z p ∘ cadBaseCoordinate n)) :=
    cad_selectedGraph_comp (cad_selectedGraph_coordinates hz (cadBaseCoordinate n)) hβ hmap
  exact cadInsertTime_graph_definable n hz (h.div (cad_selectedGraph_const hD (fun _ : Unit => 2)))

theorem cadTowerSlice_definable {ρ : Type} [Finite ρ] (n : ℕ)
    {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (hβ : CADScalarDefinable P β)
    (hS : (univ : Set ℝ).Definable Language.ring S) :
    (univ : Set ℝ).Definable Language.ring (cadTowerSlice n P β S) := by
  letI : Fintype (CADVariables ρ n) := Fintype.ofFinite _
  have hP := selectedFunctionGraph_domain_definable P (fun p (_ : Unit) => β p) hβ
  have hD := hP.preimage_comp (cadBaseCoordinate n)
  exact cad_selectedGraph_preimage
    (cadSliceInsert_selectedGraph n (coordinateSectionGraph_definable hD id) hβ (fun _ hz => hz)) hS

def CylindricalTower.slicedPath {ρ : Type} {n : ℕ} {P : Set (ρ → ℝ)}
    {β : (ρ → ℝ) → ℝ} {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S)
    (a b : CADVariables ρ n → ℝ) (t : ℝ) : CADVariables ρ n → ℝ :=
  cadDropTime n (c.endpointPath (cadSliceInsert n β a) (cadSliceInsert n β b) t)

theorem CylindricalTower.slicedPath_projection {ρ : Type} {n : ℕ}
    {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S) (a b : CADVariables ρ n → ℝ) (t : ℝ) :
    c.slicedPath a b t ∘ cadBaseCoordinate n = a ∘ cadBaseCoordinate n := by
  rw [CylindricalTower.slicedPath,cadDropTime_base,c.endpointPath_projection,
    cadSliceInsert,cadInsertTime_base]
  rfl

theorem CylindricalTower.slicedPath_mem {ρ : Type} {n : ℕ}
    {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S)
    {a b : CADVariables ρ n → ℝ} (ha : a ∈ cadTowerSlice n P β S)
    (hb : b ∈ cadTowerSlice n P β S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    c.slicedPath a b t ∈ cadTowerSlice n P β S := by
  have hproj := c.slicedPath_projection a b t
  refine ⟨hproj.symm ▸ ha.1,?_⟩
  let g := c.endpointPath (cadSliceInsert n β a) (cadSliceInsert n β b) t
  have htime : g (cadBaseCoordinate n (Sum.inr ())) = β (a ∘ cadBaseCoordinate n)/2 := by
    exact (congrFun (c.endpointPath_projection (cadSliceInsert n β a) (cadSliceInsert n β b) t)
      (Sum.inr ())).trans (congrFun (cadInsertTime_base n a _) (Sum.inr ()))
  change cadInsertTime n (c.slicedPath a b t) (β (c.slicedPath a b t ∘ cadBaseCoordinate n)/2) ∈ S
  rw [hproj,← htime]
  change cadInsertTime n (cadDropTime n g) (g (cadBaseCoordinate n (Sum.inr ()))) ∈ S
  rw [cadInsertTime_drop]
  exact c.endpointPath_mem ha.2 hb.2 ht

theorem CylindricalTower.slicedPath_properties {ρ : Type} {n : ℕ}
    {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S)
    {a b : CADVariables ρ n → ℝ} (ha : a ∈ cadTowerSlice n P β S)
    (hb : b ∈ cadTowerSlice n P β S)
    (hbase : a ∘ cadBaseCoordinate n = b ∘ cadBaseCoordinate n) :
    ContinuousOn (c.slicedPath a b) (Icc (0 : ℝ) 1) ∧
    MapsTo (c.slicedPath a b) (Icc (0 : ℝ) 1) (cadTowerSlice n P β S) ∧
    c.slicedPath a b 0 = a ∧ c.slicedPath a b 1 = b ∧
    ∀ t, c.slicedPath a b t ∘ cadBaseCoordinate n = a ∘ cadBaseCoordinate n := by
  have he : cadSliceInsert n β a ∘ cadBaseCoordinate n = cadSliceInsert n β b ∘ cadBaseCoordinate n := by
    simp only [cadSliceInsert,cadInsertTime_base,hbase]
  refine ⟨(cadDropTime_continuous n).comp_continuousOn (c.endpointPath_continuousOn ha.2 hb.2),
    fun _ ht => c.slicedPath_mem ha hb ht,?_,?_,c.slicedPath_projection a b⟩
  · rw [CylindricalTower.slicedPath,c.endpointPath_source ha.2]
    exact cadDropTime_insert n a _
  · rw [CylindricalTower.slicedPath,c.endpointPath_target _ hb.2 he]
    exact cadDropTime_insert n b _

end PaperI
