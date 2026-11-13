import PaperILean.CylindricalJointCurveSelection
import PaperILean.CylindricalRationalGraphs

/-! Joint selection from actual cylindrical sections. A leaf is selected once
per base stratum, then sampled at half its positive roof. Only the restricted
graph is glued; continuity across different base strata is not asserted.
Prospective boundary checks: evidence/checkpoint_120_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem cadPartitionGlue_vector_graph {ρ κ ι : Type} (P : Set (ρ → ℝ))
    (U : ι → Set (ρ → ℝ)) (hsub : ∀ i, U i ⊆ P)
    (hcover : ∀ p ∈ P, ∃ i, p ∈ U i)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (f : ι → (ρ → ℝ) → κ → ℝ) :
    selectedFunctionGraph P (cadPartitionGlue P U hcover f) =
      ⋃ i, selectedFunctionGraph (U i) (f i) := by
  ext v
  simp only [selectedFunctionGraph,mem_setOf_eq,mem_iUnion]
  constructor
  · rintro ⟨hp,hv⟩
    let i := cadPartitionIndex P U hcover ⟨fun r => v (Sum.inl r),hp⟩
    have hi := cadPartitionIndex_mem P U hcover ⟨fun r => v (Sum.inl r),hp⟩
    exact ⟨i,hi,by simpa only [cadPartitionGlue_on_cell P U hsub hcover hdis f hi] using hv⟩
  · rintro ⟨i,hi,hv⟩
    exact ⟨hsub i hi,by simpa only [cadPartitionGlue_on_cell P U hsub hcover hdis f hi] using hv⟩

def cadRelationLift {ρ : Type} (n : ℕ) (R : Set ((ρ ⊕ Fin n) → ℝ)) :
    Set (CADVariables (ρ ⊕ Unit) n → ℝ) :=
  {z | Sum.elim (z ∘ cadBaseCoordinate n ∘ Sum.inl) (z ∘ cadOutputCoordinate n) ∈ R}

theorem cadRelationLift_definable {ρ : Type} (n : ℕ) (R : Set ((ρ ⊕ Fin n) → ℝ))
    (hR : (univ : Set ℝ).Definable Language.ring R) :
    (univ : Set ℝ).Definable Language.ring (cadRelationLift n R) := by
  convert hR.preimage_comp
    (Sum.elim (cadBaseCoordinate n ∘ Sum.inl) (cadOutputCoordinate n)) using 1
  ext z
  change (Sum.elim (z ∘ cadBaseCoordinate n ∘ Sum.inl) (z ∘ cadOutputCoordinate n) ∈ R) ↔ (z ∘ Sum.elim (cadBaseCoordinate n ∘ Sum.inl) (cadOutputCoordinate n)) ∈ R
  have he : Sum.elim (z ∘ cadBaseCoordinate n ∘ Sum.inl) (z ∘ cadOutputCoordinate n) =
      z ∘ Sum.elim (cadBaseCoordinate n ∘ Sum.inl) (cadOutputCoordinate n) := by
    funext k
    cases k <;> rfl
  rw [he]

theorem cadRelationLift_nonempty {ρ : Type} (n : ℕ) (P : Set (ρ → ℝ))
    (R : Set ((ρ ⊕ Fin n) → ℝ))
    (hR : ∀ p ∈ P, ∃ x, Sum.elim p x ∈ R) :
    ∀ p ∈ P, ∀ t ∈ Ioo (0 : ℝ) 1,
      ∃ x, cadPack n (Sum.elim p (fun _ : Unit => t)) x ∈ cadRelationLift n R := by
  intro p hp t _
  obtain ⟨x,hx⟩ := hR p hp
  refine ⟨x,?_⟩
  change Sum.elim
    ((cadPack n (Sum.elim p (fun _ : Unit => t)) x ∘ cadBaseCoordinate n) ∘ Sum.inl)
    (cadPack n (Sum.elim p (fun _ : Unit => t)) x ∘ cadOutputCoordinate n) ∈ R
  rwa [cadPack_base,cadPack_output]

def CylindricalTower.halfRoofSection {ρ : Type} {n : ℕ} {P : Set (ρ → ℝ)}
    {β : (ρ → ℝ) → ℝ} {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S) (p : ρ → ℝ) : Fin n → ℝ :=
  c.sectionMap (Sum.elim p (fun _ : Unit => β p/2)) ∘ cadOutputCoordinate n

theorem CylindricalTower.halfRoofSection_graph {ρ : Type} [Finite ρ]
    {n : ℕ} {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S)
    (hβ : CADScalarDefinable P β) (hpos : ∀ p ∈ P, 0 < β p) :
    (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P c.halfRoofSection) := by
  letI : Fintype ρ := Fintype.ofFinite ρ
  have hP := selectedFunctionGraph_domain_definable P (fun p (_ : Unit) => β p) hβ
  have ht : CADScalarDefinable P (fun p => β p/2) :=
    hβ.div (cad_selectedGraph_const hP (fun _ : Unit => 2))
  have hpair := cad_selectedGraph_pair (coordinateSectionGraph_definable hP id) ht
  have hmap : MapsTo (fun p => Sum.elim p (fun _ : Unit => β p/2)) P (cadInitialBand P β) := by
    intro p hp
    exact ⟨hp,half_pos (hpos p hp),by change β p/2 < β p; linarith [hpos p hp]⟩
  exact cad_selectedGraph_coordinates
    (cad_selectedGraph_comp hpair (c.sectionMap_graph_definable (cadInitialBand_definable hβ)) hmap)
    (cadOutputCoordinate n)

theorem CylindricalTower.halfRoofSection_mem {ρ : Type} {n : ℕ}
    {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S)
    {R : Set ((ρ ⊕ Fin n) → ℝ)} (hS : S ⊆ cadRelationLift n R)
    {p : ρ → ℝ} (hp : p ∈ P) (hpos : 0 < β p) :
    Sum.elim p (c.halfRoofSection p) ∈ R := by
  have ht : Sum.elim p (fun _ : Unit => β p/2) ∈ cadInitialBand P β :=
    ⟨hp,half_pos hpos,by change β p/2 < β p; linarith⟩
  have h := hS (c.sectionMap_mem ht)
  change Sum.elim
    ((c.sectionMap (Sum.elim p (fun _ : Unit => β p/2)) ∘ cadBaseCoordinate n) ∘ Sum.inl)
    (c.halfRoofSection p) ∈ R at h
  rwa [c.sectionMap_projection] at h

theorem published_cylindrical_selector_fin
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ) (P : Set (ρ → ℝ))
    (R : Set ((ρ ⊕ Fin n) → ℝ))
    (hP : HasPolynomialSignDescription P) (hR : HasPolynomialSignDescription R)
    (hne : ∀ p ∈ P, ∃ x, Sum.elim p x ∈ R) :
    ∃ f : (ρ → ℝ) → Fin n → ℝ,
      HasPolynomialSignDescription (selectedFunctionGraph P f) ∧
      ∀ p ∈ P, Sum.elim p (f p) ∈ R := by
  classical
  obtain ⟨d⟩ := hCAD.decomposition n P (cadRelationLift n R) hP
    (hQE.finite_sign_description _ (cadRelationLift_definable n R
      (hasPolynomialSignDescription_definable hR)))
  choose leaf hleaf using d.exists_cell_subset (cadRelationLift_nonempty n P R hne)
  let f := fun i => (d.tower i (leaf i)).halfRoofSection
  refine ⟨cadPartitionGlue P d.base d.base_cover f,?_,?_⟩
  · apply hQE.finite_sign_description
    rw [cadPartitionGlue_vector_graph P d.base d.base_subset d.base_cover d.base_disjoint]
    exact cad_definable_finite_iUnion (fun i =>
      (d.tower i (leaf i)).halfRoofSection_graph (d.roof i).graph_definable (d.roof_positive i))
  · intro p hp
    obtain ⟨i,hi⟩ := d.base_cover p hp
    rw [cadPartitionGlue_on_cell P d.base d.base_subset d.base_cover d.base_disjoint f hi]
    exact (d.tower i (leaf i)).halfRoofSection_mem (hleaf i) hi (d.roof_positive i p hi)

end PaperI
