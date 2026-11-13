import PaperILean.CylindricalSlicedFamilies

/-! A common path-format budget for all leaves and all endpoint pairs of one
joint finite sliced family. The family is chosen before the endpoints. These
budgets can still depend on the input family P,E; full ambient-format whole-chain
uniformity and the attachment selection are separate, unresolved obligations. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable

def CylindricalInitialBandDecomposition.slicedCellPath {ρ : Type} {n : ℕ}
    {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) (j : d.slicedLeaf)
    (a b : CADVariables ρ n → ℝ) : ℝ → CADVariables ρ n → ℝ :=
  (d.tower j.val.1 j.val.2).slicedPath a b

theorem CylindricalInitialBandDecomposition.slicedCellPath_jointGraph_definable
    {ρ : Type} [Finite ρ] {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) (j : d.slicedLeaf) :
    (univ : Set ℝ).Definable Language.ring
      (jointUnitPathGraph (cadTowerEndpointPairs n (d.slicedCell j))
        (fun v => d.slicedCellPath j (v ∘ Sum.inl) (v ∘ Sum.inr))) := by
  letI : Fintype (CADVariables ρ n) := Fintype.ofFinite _
  have hD := cadTowerEndpointPairs_definable n (d.slicedCell_definable j)
  exact (d.tower j.val.1 j.val.2).slicedPath_jointGraph_definable (d.roof j.val.1).graph_definable
    (coordinateSectionGraph_definable hD Sum.inl) (coordinateSectionGraph_definable hD Sum.inr)
    (fun _ hv => hv.1) (fun _ hv => hv.2.1)

theorem published_cylindrical_slicedFamily_uniform_format
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) :
    ∃ sPath dPath : ℕ, ∀ j : d.slicedLeaf, ∀ a ∈ d.slicedCell j, ∀ b ∈ d.slicedCell j,
      a ∘ cadBaseCoordinate n = b ∘ cadBaseCoordinate n →
      ∃ γ : SemialgebraicUnitPath (d.slicedCell j) a b,
        γ.toFun = d.slicedCellPath j a b ∧
        (∀ t, γ.toFun t ∘ cadBaseCoordinate n = a ∘ cadBaseCoordinate n) ∧
        ∃ A : Finset (MvPolynomial (Unit ⊕ CADVariables ρ n) ℝ),
          A.card ≤ sPath ∧ (∀ q ∈ A, q.totalDegree ≤ dPath) ∧
          PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  classical
  have h := fun j : d.slicedLeaf => published_cylindrical_slicedPaths_bounded_format hQE
    (d.tower j.val.1 j.val.2) (d.roof j.val.1).graph_definable
  choose sp dp hpath using h
  refine ⟨Finset.univ.sup sp,Finset.univ.sup dp,?_⟩
  intro j a ha b hb hbase
  obtain ⟨γ,hγ,hproj,A,hs,hd,hA⟩ := hpath j a ha b hb hbase
  exact ⟨γ,hγ,hproj,A,hs.trans (Finset.le_sup (f := sp) (Finset.mem_univ j)),
    fun q hq => (hd q hq).trans (Finset.le_sup (f := dp) (Finset.mem_univ j)),hA⟩

theorem published_cylindrical_finite_sliced_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ) (P : Set (ρ → ℝ)) (E : Set (CADVariables ρ n → ℝ))
    (hP : HasPolynomialSignDescription P) (hE : HasPolynomialSignDescription E) :
    ∃ d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E), ∃ sPath dPath : ℕ,
      (∀ z, (∃ j : d.slicedLeaf, z ∈ d.slicedCell j) ↔ z ∈ E ∧ z ∘ cadBaseCoordinate n ∈ P) ∧
      (∀ j : d.slicedLeaf, d.slicedCell j ⊆ E ∧ HasPolynomialSignDescription (d.slicedCell j) ∧
        HasPolynomialSignDescription (jointUnitPathGraph (cadTowerEndpointPairs n (d.slicedCell j))
          (fun v => d.slicedCellPath j (v ∘ Sum.inl) (v ∘ Sum.inr)))) ∧
      ∀ j : d.slicedLeaf, ∀ a ∈ d.slicedCell j, ∀ b ∈ d.slicedCell j,
        a ∘ cadBaseCoordinate n = b ∘ cadBaseCoordinate n →
        ∃ γ : SemialgebraicUnitPath (d.slicedCell j) a b,
          γ.toFun = d.slicedCellPath j a b ∧
          (∀ t, γ.toFun t ∘ cadBaseCoordinate n = a ∘ cadBaseCoordinate n) ∧
          ∃ A : Finset (MvPolynomial (Unit ⊕ CADVariables ρ n) ℝ),
            A.card ≤ sPath ∧ (∀ q ∈ A, q.totalDegree ≤ dPath) ∧
            PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨d⟩ := published_cylindrical_timeCylinder_decomposition hCAD hQE n P E hP hE
  obtain ⟨sp,dp,hpath⟩ := published_cylindrical_slicedFamily_uniform_format hQE d
  refine ⟨d,sp,dp,d.slicedCell_cover_iff,?_,hpath⟩
  intro j
  exact ⟨d.slicedCell_subset j,hQE.finite_sign_description _ (d.slicedCell_definable j),
    hQE.finite_sign_description _ (d.slicedCellPath_jointGraph_definable j)⟩

end PaperI
