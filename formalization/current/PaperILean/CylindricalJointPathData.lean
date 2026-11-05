import PaperILean.JointPathAssembly

/-! Actual slice and directed-edge paths in the ambient fiber, packaged with
their joint graph. All endpoint sections are retained; no path oracle is used. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem CylindricalInitialBandDecomposition.slicedFiberCell_subset
    {ρ : Type} {n : ℕ} {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E)) (j : d.slicedLeaf)
    (p : ρ → ℝ) :
    projectionFiber (d.slicedFiberCell j) p ⊆ projectionFiber (cadPackedRelation n E) p := by
  intro x hx
  exact d.slicedCell_subset j hx

theorem published_cylindrical_slice_jointPath
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] {n : ℕ} {T P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E)) (j : d.slicedLeaf)
    (x y : (ρ → ℝ) → Fin n → ℝ)
    (hX : HasPolynomialSignDescription (selectedFunctionGraph P x))
    (hY : HasPolynomialSignDescription (selectedFunctionGraph P y))
    (hx : ∀ p ∈ P, x p ∈ projectionFiber (d.slicedFiberCell j) p)
    (hy : ∀ p ∈ P, y p ∈ projectionFiber (d.slicedFiberCell j) p) :
    Nonempty (JointSemialgebraicPath P (cadPackedRelation n E) x y) := by
  have hG := hQE.finite_sign_description _
    ((d.tower j.val.1 j.val.2).slicedFiberPath_jointGraph_definable (d.roof j.val.1).graph_definable
      (hasPolynomialSignDescription_definable hX) (hasPolynomialSignDescription_definable hY) hx hy)
  obtain ⟨_,_,hpath⟩ := published_cylindrical_slicedFiberPath_bounded_unitPaths hQE
    (d.tower j.val.1 j.val.2) (d.roof j.val.1).graph_definable x y hX hY hx hy
  refine ⟨⟨(fun p => (d.tower j.val.1 j.val.2).slicedFiberPath p (x p) (y p)),hG,?_⟩⟩
  intro p hp
  obtain ⟨γ,hγ,_⟩ := hpath p hp
  exact ⟨γ.weaken (d.slicedFiberCell_subset j p),hγ⟩

theorem published_cylindrical_directed_jointPath
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] {n : ℕ} {T P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E)) (j k : d.slicedLeaf)
    (x y : (ρ → ℝ) → Fin n → ℝ)
    (hPD : P ⊆ directedCellAttachmentDomain (d.slicedFiberCell j) (d.slicedFiberCell k))
    (hX : HasPolynomialSignDescription (selectedFunctionGraph P x))
    (hY : HasPolynomialSignDescription (selectedFunctionGraph P y))
    (hx : ∀ p ∈ P, x p ∈ projectionFiber (d.slicedFiberCell j) p)
    (hy : ∀ p ∈ P, y p ∈ projectionFiber (d.slicedFiberCell k) p) :
    Nonempty (JointSemialgebraicPath P (cadPackedRelation n E) x y) := by
  obtain ⟨a,ε,g,_,_,_,_,_,hG,_,hpath⟩ :=
    published_cylindrical_directed_sliced_paths hCAD hQE d j k P x y hPD hX hY hx hy
  refine ⟨⟨d.slicedAttachmentPath j k x y a ε g,hG,?_⟩⟩
  intro p hp
  obtain ⟨γ,hγ,_⟩ := hpath p hp (projectionFiber (cadPackedRelation n E) p)
    (d.slicedFiberCell_subset j p) (d.slicedFiberCell_subset k p)
  exact ⟨γ,hγ⟩

end PaperI
