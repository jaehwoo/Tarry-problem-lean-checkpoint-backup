import PaperILean.CylindricalFiberCoordinates

/-! The existing sliced paths expressed in the actual output fiber, with
jointly varying endpoints. Parameter coordinates stay fixed by construction.
These are paths in the same actual slice, not in a closure or total-space fiber. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def CylindricalTower.slicedFiberPath {ρ : Type} {n : ℕ} {U : Set (ρ → ℝ)}
    {β : (ρ → ℝ) → ℝ} {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand U β) S) (p : ρ → ℝ) (a b : Fin n → ℝ)
    (t : ℝ) : Fin n → ℝ :=
  c.slicedPath (cadPack n p a) (cadPack n p b) t ∘ cadOutputCoordinate n

theorem CylindricalTower.slicedFiberPath_properties {ρ : Type} {n : ℕ}
    {U : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand U β) S)
    {p : ρ → ℝ} {a b : Fin n → ℝ}
    (ha : a ∈ projectionFiber (cadPackedRelation n (cadTowerSlice n U β S)) p)
    (hb : b ∈ projectionFiber (cadPackedRelation n (cadTowerSlice n U β S)) p) :
    ContinuousOn (c.slicedFiberPath p a b) (Icc (0 : ℝ) 1) ∧
    MapsTo (c.slicedFiberPath p a b) (Icc (0 : ℝ) 1)
      (projectionFiber (cadPackedRelation n (cadTowerSlice n U β S)) p) ∧
    c.slicedFiberPath p a b 0 = a ∧ c.slicedFiberPath p a b 1 = b := by
  rw [cadPackedRelation_fiber] at ha hb
  have h := c.slicedPath_properties ha hb (by rw [cadPack_base,cadPack_base])
  refine ⟨continuousOn_pi.mpr (fun i => (continuous_apply _).comp_continuousOn h.1),?_,?_,?_⟩
  · intro t ht
    rw [cadPackedRelation_fiber]
    change cadPack n p (c.slicedPath (cadPack n p a) (cadPack n p b) t ∘ cadOutputCoordinate n) ∈ cadTowerSlice n U β S
    have hp : c.slicedPath (cadPack n p a) (cadPack n p b) t ∘ cadBaseCoordinate n = p := by
      rw [c.slicedPath_projection,cadPack_base]
    have he := cadPack_reconstruct n (c.slicedPath (cadPack n p a) (cadPack n p b) t)
    rw [hp] at he
    rw [he]
    exact h.2.1 ht
  · change c.slicedPath (cadPack n p a) (cadPack n p b) 0 ∘ cadOutputCoordinate n = a
    rw [h.2.2.1,cadPack_output]
  · change c.slicedPath (cadPack n p a) (cadPack n p b) 1 ∘ cadOutputCoordinate n = b
    rw [h.2.2.2.1,cadPack_output]

theorem CylindricalTower.slicedFiberPath_jointGraph_definable
    {ρ : Type} [Finite ρ] {n : ℕ} {U P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand U β) S) (hβ : CADScalarDefinable U β)
    {a b : (ρ → ℝ) → Fin n → ℝ}
    (hA : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P a))
    (hB : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P b))
    (ha : ∀ p ∈ P, a p ∈ projectionFiber (cadPackedRelation n (cadTowerSlice n U β S)) p)
    (hb : ∀ p ∈ P, b p ∈ projectionFiber (cadPackedRelation n (cadTowerSlice n U β S)) p) :
    (univ : Set ℝ).Definable Language.ring
      (jointUnitPathGraph P (fun p => c.slicedFiberPath p (a p) (b p))) := by
  letI : Fintype ρ := Fintype.ofFinite ρ
  have hP := selectedFunctionGraph_domain_definable P a hA
  have hid := coordinateSectionGraph_definable hP (id : ρ → ρ)
  have hPA := cadPack_selectedGraph n hid hA
  have hPB := cadPack_selectedGraph n hid hB
  let V := cadPathParameterDomain P
  have hV := cadPathParameterDomain_definable hP
  have hproj := coordinateSectionGraph_definable hV (Sum.inl : ρ → ρ ⊕ Unit)
  have hmap : MapsTo (fun v : (ρ ⊕ Unit) → ℝ => v ∘ Sum.inl) V P := fun _ hv => hv.1
  have hA' := cad_selectedGraph_comp hproj hPA hmap
  have hB' := cad_selectedGraph_comp hproj hPB hmap
  have hT : CADScalarDefinable V (fun v => v (Sum.inr ())) :=
    coordinateSectionGraph_definable hV (fun _ : Unit => Sum.inr ())
  have h := c.slicedPath_selectedGraph hβ hA' hB' hT
    (fun _ hv => ha _ hv.1) (fun _ hv => hb _ hv.1) (fun _ hv => hv.2)
  have ho := cad_selectedGraph_coordinates h (cadOutputCoordinate n)
  let e : (ρ ⊕ Unit) ⊕ Fin n → ρ ⊕ (Unit ⊕ Fin n) :=
    Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)
  convert ho.preimage_comp e using 1
  ext z
  change (z ∘ Sum.inl ∈ P ∧ _ ∈ unitPathGraph _) ↔ _
  simp only [selectedFunctionGraph,cadPathParameterDomain,V,jointUnitPathGraph,unitPathGraph,
    mem_setOf_eq,mem_preimage,Function.comp_def,e,Sum.elim_inl,Sum.elim_inr,funext_iff,
    CylindricalTower.slicedFiberPath,Function.id_def]
  constructor
  · rintro ⟨hp,ht,he⟩
    exact ⟨⟨hp,ht⟩,fun i => (he i).symm⟩
  · rintro ⟨⟨hp,ht⟩,he⟩
    exact ⟨hp,ht,fun i => (he i).symm⟩

theorem published_cylindrical_slicedFiberPath_bounded_unitPaths
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] {n : ℕ} {U P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand U β) S) (hβ : CADScalarDefinable U β)
    (a b : (ρ → ℝ) → Fin n → ℝ)
    (hA : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hB : HasPolynomialSignDescription (selectedFunctionGraph P b))
    (ha : ∀ p ∈ P, a p ∈ projectionFiber (cadPackedRelation n (cadTowerSlice n U β S)) p)
    (hb : ∀ p ∈ P, b p ∈ projectionFiber (cadPackedRelation n (cadTowerSlice n U β S)) p) :
    ∃ s d : ℕ, ∀ p ∈ P,
      ∃ γ : SemialgebraicUnitPath
        (projectionFiber (cadPackedRelation n (cadTowerSlice n U β S)) p) (a p) (b p),
        γ.toFun = c.slicedFiberPath p (a p) (b p) ∧
        ∃ A : Finset (MvPolynomial (Unit ⊕ Fin n) ℝ), A.card ≤ s ∧
          (∀ q ∈ A, q.totalDegree ≤ d) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  have hJoint := hQE.finite_sign_description _ (c.slicedFiberPath_jointGraph_definable hβ
    (hasPolynomialSignDescription_definable hA) (hasPolynomialSignDescription_definable hB) ha hb)
  obtain ⟨s,d,hfmt⟩ := jointUnitPathGraph_uniform_fiber_format _ _ hJoint
  refine ⟨s,d,?_⟩
  intro p hp
  obtain ⟨A,hs,hd,hA⟩ := hfmt p hp
  have h := c.slicedFiberPath_properties (ha p hp) (hb p hp)
  exact ⟨⟨c.slicedFiberPath p (a p) (b p),h.1,h.2.1,h.2.2.1,h.2.2.2,⟨A,hA⟩⟩,rfl,A,hs,hd,hA⟩

end PaperI
