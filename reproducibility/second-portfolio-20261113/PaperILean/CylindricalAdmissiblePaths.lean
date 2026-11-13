import PaperILean.AdmissibleChainDomains

/-! Construct actual joint paths on the finite-chain admissible domain.
The domain is defined from actual sliced cells and their eligibility relations,
not from the desired path conclusion. Unrelated fibers may be disconnected. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable

theorem published_cylindrical_admissible_jointPath
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] {n : ℕ} {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E))
    (P : Set (ρ → ℝ)) (x y : (ρ → ℝ) → Fin n → ℝ)
    (hP : HasPolynomialSignDescription P)
    (hX : HasPolynomialSignDescription (selectedFunctionGraph P x))
    (hY : HasPolynomialSignDescription (selectedFunctionGraph P y)) :
    Nonempty (JointSemialgebraicPath (orientedChainSectionDomain P d.slicedFiberCell x y)
      (cadPackedRelation n E) x y) := by
  classical
  letI : Fintype ρ := Fintype.ofFinite ρ
  let R := orientedChainSectionDomain P d.slicedFiberCell x y
  let D := fun c : OrientedBoundedCellChain d.slicedLeaf =>
    {p | p ∈ P ∧ Sum.elim (Sum.elim p (x p)) (y p) ∈ orientedCellChainEligibility d.slicedFiberCell c}
  have hPdef := hasPolynomialSignDescription_definable hP
  have hRdef := orientedChainSectionDomain_definable P d.slicedFiberCell x y hPdef
    d.slicedFiberCell_definable (hasPolynomialSignDescription_definable hX)
    (hasPolynomialSignDescription_definable hY)
  have hencode := cad_selectedGraph_pair
    (cad_selectedGraph_pair (coordinateSectionGraph_definable hPdef (id : ρ → ρ))
      (hasPolynomialSignDescription_definable hX)) (hasPolynomialSignDescription_definable hY)
  have hD : ∀ c, (univ : Set ℝ).Definable Language.ring (D c) := fun c =>
    cad_selectedGraph_preimage hencode
      (orientedCellChainEligibility_definable _ d.slicedFiberCell_definable c)
  have hcover : ∀ p ∈ R, ∃ c, p ∈ D c := fun _ ⟨hp,c,hc⟩ => ⟨c,hp,hc⟩
  obtain ⟨pick,hpick,hregion⟩ := finite_definable_selector_on R D hRdef hD hcover
  have hpaths : ∀ c, Nonempty (JointSemialgebraicPath (finiteSelectorRegion R pick c)
      (cadPackedRelation n E) x y) := by
    intro c
    have hA := hQE.finite_sign_description _ (hregion c)
    have hAP : finiteSelectorRegion R pick c ⊆ P := fun _ hp =>
      (finiteSelectorRegion_subset R pick c hp).1
    apply published_cylindrical_oriented_chain_jointPath hCAD hQE d c _ x y hA
      (selectedFunctionGraph_restrict hAP x hA hX) (selectedFunctionGraph_restrict hAP y hA hY)
    rintro p ⟨hp,hc⟩
    have h := (hpick ⟨p,hp⟩).2
    rwa [hc] at h
  exact ⟨JointSemialgebraicPath.glue hQE R (cadPackedRelation n E) x y pick
    (fun c => Classical.choice (hpaths c))⟩

end PaperI
