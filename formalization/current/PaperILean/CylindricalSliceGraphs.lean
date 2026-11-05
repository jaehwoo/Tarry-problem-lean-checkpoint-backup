import PaperILean.CylindricalSlicedPaths

/-! Exact joint graphs and endpoint-uniform format for the actual sliced path.
The bounds here belong to one supplied tower; no ambient-format or complete
cell-chain bound is inferred from this local theorem. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem CylindricalTower.slicedPath_selectedGraph
    {α ρ : Type} [Finite α] [Finite ρ] {D : Set (α → ℝ)}
    {n : ℕ} {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S) (hβ : CADScalarDefinable P β)
    {a b : (α → ℝ) → CADVariables ρ n → ℝ} {t : (α → ℝ) → ℝ}
    (hA : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D a))
    (hB : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D b))
    (hT : CADScalarDefinable D t)
    (ha : MapsTo a D (cadTowerSlice n P β S)) (hb : MapsTo b D (cadTowerSlice n P β S))
    (ht : MapsTo t D (Icc (0 : ℝ) 1)) :
    (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph D (fun p => c.slicedPath (a p) (b p) (t p))) := by
  have h := c.endpointPath_selectedGraph
    (cadSliceInsert_selectedGraph n hA hβ (fun _ hp => (ha hp).1))
    (cadSliceInsert_selectedGraph n hB hβ (fun _ hp => (hb hp).1))
    hT (fun _ hp => (ha hp).2) (fun _ hp => (hb hp).2) ht
  exact cad_selectedGraph_coordinates h (cadKeepCoordinate n)

theorem CylindricalTower.slicedPath_jointGraph_definable
    {α ρ : Type} [Finite α] [Finite ρ] {D : Set (α → ℝ)}
    {n : ℕ} {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S) (hβ : CADScalarDefinable P β)
    {a b : (α → ℝ) → CADVariables ρ n → ℝ}
    (hA : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D a))
    (hB : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D b))
    (ha : MapsTo a D (cadTowerSlice n P β S)) (hb : MapsTo b D (cadTowerSlice n P β S)) :
    (univ : Set ℝ).Definable Language.ring
      (jointUnitPathGraph D (fun p => c.slicedPath (a p) (b p))) := by
  let V := cadPathParameterDomain D
  have hD := selectedFunctionGraph_domain_definable D a hA
  have hV := cadPathParameterDomain_definable hD
  letI : Fintype α := Fintype.ofFinite α
  have hproj := coordinateSectionGraph_definable hV (Sum.inl : α → α ⊕ Unit)
  have hmap : MapsTo (fun v : (α ⊕ Unit) → ℝ => v ∘ Sum.inl) V D := fun _ hv => hv.1
  have hA' := cad_selectedGraph_comp hproj hA hmap
  have hB' := cad_selectedGraph_comp hproj hB hmap
  have hT : CADScalarDefinable V (fun v => v (Sum.inr ())) :=
    coordinateSectionGraph_definable hV (fun _ : Unit => Sum.inr ())
  have h := c.slicedPath_selectedGraph hβ hA' hB' hT
    (fun _ hv => ha hv.1) (fun _ hv => hb hv.1) (fun _ hv => hv.2)
  let e : (α ⊕ Unit) ⊕ CADVariables ρ n → α ⊕ (Unit ⊕ CADVariables ρ n) :=
    Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)
  convert h.preimage_comp e using 1
  ext z
  change (z ∘ Sum.inl ∈ D ∧ _ ∈ unitPathGraph _) ↔ _
  simp only [selectedFunctionGraph,cadPathParameterDomain,V,jointUnitPathGraph,unitPathGraph,
    mem_setOf_eq,mem_preimage,Function.comp_def,e,Sum.elim_inl,Sum.elim_inr,funext_iff]
  constructor
  · rintro ⟨hp,ht,he⟩
    exact ⟨⟨hp,ht⟩,fun i => (he i).symm⟩
  · rintro ⟨⟨hp,ht⟩,he⟩
    exact ⟨hp,ht,fun i => (he i).symm⟩

theorem published_cylindrical_slicedPath_joint_semialgebraic
    (hQE : PublishedRealSemialgebraicity) {ρ : Type} [Finite ρ]
    {n : ℕ} {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S) (hβ : CADScalarDefinable P β) :
    HasPolynomialSignDescription (jointUnitPathGraph (cadTowerEndpointPairs n (cadTowerSlice n P β S))
      (fun v => c.slicedPath (v ∘ Sum.inl) (v ∘ Sum.inr))) := by
  letI : Fintype (CADVariables ρ n) := Fintype.ofFinite _
  have hS := cadTowerSlice_definable n hβ (c.region_definable (cadInitialBand_definable hβ))
  have hD := cadTowerEndpointPairs_definable n hS
  exact hQE.finite_sign_description _ (c.slicedPath_jointGraph_definable hβ
    (coordinateSectionGraph_definable hD Sum.inl) (coordinateSectionGraph_definable hD Sum.inr)
    (fun _ hv => hv.1) (fun _ hv => hv.2.1))

theorem published_cylindrical_slicedPaths_bounded_format
    (hQE : PublishedRealSemialgebraicity) {ρ : Type} [Finite ρ]
    {n : ℕ} {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S) (hβ : CADScalarDefinable P β) :
    ∃ sPath dPath : ℕ, ∀ a ∈ cadTowerSlice n P β S, ∀ b ∈ cadTowerSlice n P β S,
      a ∘ cadBaseCoordinate n = b ∘ cadBaseCoordinate n →
      ∃ γ : SemialgebraicUnitPath (cadTowerSlice n P β S) a b,
        γ.toFun = c.slicedPath a b ∧
        (∀ t, γ.toFun t ∘ cadBaseCoordinate n = a ∘ cadBaseCoordinate n) ∧
        ∃ A : Finset (MvPolynomial (Unit ⊕ CADVariables ρ n) ℝ),
          A.card ≤ sPath ∧ (∀ q ∈ A, q.totalDegree ≤ dPath) ∧
          PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨sPath,dPath,hfmt⟩ := jointUnitPathGraph_uniform_fiber_format _ _
    (published_cylindrical_slicedPath_joint_semialgebraic hQE c hβ)
  refine ⟨sPath,dPath,?_⟩
  intro a ha b hb hbase
  have hp : Sum.elim a b ∈ cadTowerEndpointPairs n (cadTowerSlice n P β S) := ⟨ha,hb,hbase⟩
  obtain ⟨A,hs,hd,hA⟩ := hfmt (Sum.elim a b) hp
  have h := c.slicedPath_properties ha hb hbase
  exact ⟨⟨c.slicedPath a b,h.1,h.2.1,h.2.2.1,h.2.2.2.1,⟨A,hA⟩⟩,
    rfl,h.2.2.2.2,A,hs,hd,hA⟩

end PaperI
