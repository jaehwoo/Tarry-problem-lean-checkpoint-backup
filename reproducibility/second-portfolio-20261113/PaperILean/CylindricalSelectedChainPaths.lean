import PaperILean.CylindricalOrientedChainPaths

/-! Finite definable choice of the whole oriented chain, followed by actual
path construction and gluing. No continuity in the external parameter is
asserted. Connectivity is used only on the active parameter domain. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem CylindricalInitialBandDecomposition.slicedFiberCell_cover
    {ρ : Type} {n : ℕ} {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E))
    {p : ρ → ℝ} (hp : p ∈ T) {x : Fin n → ℝ}
    (hx : x ∈ projectionFiber (cadPackedRelation n E) p) :
    ∃ j : d.slicedLeaf, x ∈ projectionFiber (d.slicedFiberCell j) p := by
  rw [cadPackedRelation_fiber] at hx
  obtain ⟨j,hj⟩ := d.slicedCell_cover hx (by simpa only [cadPack_base] using hp)
  exact ⟨j,hj⟩

theorem published_cylindrical_selected_chain_jointPath
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] {n : ℕ} {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E))
    (P : Set (ρ → ℝ)) (x y : (ρ → ℝ) → Fin n → ℝ)
    (hP : HasPolynomialSignDescription P) (hPT : P ⊆ T)
    (hX : HasPolynomialSignDescription (selectedFunctionGraph P x))
    (hY : HasPolynomialSignDescription (selectedFunctionGraph P y))
    (hconn : ∀ p ∈ P, IsPreconnected (projectionFiber (cadPackedRelation n E) p))
    (hx : ∀ p ∈ P, x p ∈ projectionFiber (cadPackedRelation n E) p)
    (hy : ∀ p ∈ P, y p ∈ projectionFiber (cadPackedRelation n E) p) :
    Nonempty (JointSemialgebraicPath P (cadPackedRelation n E) x y) := by
  classical
  letI : Fintype ρ := Fintype.ofFinite ρ
  let encode := fun p => Sum.elim (Sum.elim p (x p)) (y p)
  let D := fun c : OrientedBoundedCellChain d.slicedLeaf =>
    {p | p ∈ P ∧ encode p ∈ orientedCellChainEligibility d.slicedFiberCell c}
  have hPdef := hasPolynomialSignDescription_definable hP
  have hencode := cad_selectedGraph_pair
    (cad_selectedGraph_pair (coordinateSectionGraph_definable hPdef (id : ρ → ρ))
      (hasPolynomialSignDescription_definable hX)) (hasPolynomialSignDescription_definable hY)
  have hD : ∀ c, (univ : Set ℝ).Definable Language.ring (D c) := fun c =>
    cad_selectedGraph_preimage hencode
      (orientedCellChainEligibility_definable _ d.slicedFiberCell_definable c)
  have hcover : ∀ p ∈ P, ∃ c, p ∈ D c := by
    intro p hp
    obtain ⟨c,hc⟩ := connected_finite_cover_has_cellChainEligibility d.slicedFiberCell p
      (projectionFiber (cadPackedRelation n E) p) (hconn p hp)
      (fun j => d.slicedFiberCell_subset j p)
      (fun _ hz => d.slicedFiberCell_cover (hPT hp) hz) (x p) (y p) (hx p hp) (hy p hp)
    obtain ⟨σ,hσ⟩ := cellChainEligibility_has_orientation d.slicedFiberCell c hc
    exact ⟨⟨c,σ⟩,hp,hσ⟩
  obtain ⟨pick,hpick,hregion⟩ := finite_definable_selector_on P D hPdef hD hcover
  have hpaths : ∀ c, Nonempty (JointSemialgebraicPath (finiteSelectorRegion P pick c)
      (cadPackedRelation n E) x y) := by
    intro c
    have hR := hQE.finite_sign_description _ (hregion c)
    apply published_cylindrical_oriented_chain_jointPath hCAD hQE d c _ x y hR
      (selectedFunctionGraph_restrict (finiteSelectorRegion_subset P pick c) x hR hX)
      (selectedFunctionGraph_restrict (finiteSelectorRegion_subset P pick c) y hR hY)
    rintro p ⟨hp,hc⟩
    have h := (hpick ⟨p,hp⟩).2
    rwa [hc] at h
  exact ⟨JointSemialgebraicPath.glue hQE P (cadPackedRelation n E) x y pick
    (fun c => Classical.choice (hpaths c))⟩

end PaperI
