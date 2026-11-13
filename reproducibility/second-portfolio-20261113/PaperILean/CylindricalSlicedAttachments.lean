import PaperILean.CylindricalAttachmentGerms
import PaperILean.CylindricalFiberPaths

/-! Directed edges of the finite sliced family: the source-slice path, an
actual CAD germ restricted to half its radius, then the target-slice path.
All three paths and both joins are the same jointly defined objects. This
module does not select or concatenate a complete cell chain. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def CylindricalInitialBandDecomposition.slicedFiberCell {ρ : Type} {n : ℕ}
    {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E)) (j : d.slicedLeaf) :
    Set ((ρ ⊕ Fin n) → ℝ) := cadPackedRelation n (d.slicedCell j)

theorem CylindricalInitialBandDecomposition.slicedFiberCell_definable
    {ρ : Type} [Finite ρ] {n : ℕ} {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E)) (j : d.slicedLeaf) :
    (univ : Set ℝ).Definable Language.ring (d.slicedFiberCell j) :=
  cadPackedRelation_definable n (d.slicedCell_definable j)

def CylindricalInitialBandDecomposition.slicedAttachmentPath {ρ : Type} {n : ℕ}
    {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E))
    (j k : d.slicedLeaf) (x y a : (ρ → ℝ) → Fin n → ℝ)
    (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → Fin n → ℝ)
    (p : ρ → ℝ) : ℝ → Fin n → ℝ :=
  unitPathConcat ((d.tower j.val.1 j.val.2).slicedFiberPath p (x p) (a p))
    (unitPathConcat (jointHalfRadiusPath ε g p)
      ((d.tower k.val.1 k.val.2).slicedFiberPath p (g p (ε p/2)) (y p)))

theorem published_cylindrical_slicedAttachmentPath_semialgebraic
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] {n : ℕ} {T P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E))
    (j k : d.slicedLeaf) (x y a : (ρ → ℝ) → Fin n → ℝ)
    (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → Fin n → ℝ)
    (hX : HasPolynomialSignDescription (selectedFunctionGraph P x))
    (hY : HasPolynomialSignDescription (selectedFunctionGraph P y))
    (hA : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hB : HasPolynomialSignDescription (selectedFunctionGraph P (fun p => g p (ε p/2))))
    (hG : HasPolynomialSignDescription (jointUnitPathGraph P (jointHalfRadiusPath ε g)))
    (hx : ∀ p ∈ P, x p ∈ projectionFiber (d.slicedFiberCell j) p)
    (hy : ∀ p ∈ P, y p ∈ projectionFiber (d.slicedFiberCell k) p)
    (ha : ∀ p ∈ P, a p ∈ projectionFiber (d.slicedFiberCell j) p)
    (hb : ∀ p ∈ P, g p (ε p/2) ∈ projectionFiber (d.slicedFiberCell k) p) :
    HasPolynomialSignDescription (jointUnitPathGraph P (d.slicedAttachmentPath j k x y a ε g)) := by
  have hL := hQE.finite_sign_description _
    ((d.tower j.val.1 j.val.2).slicedFiberPath_jointGraph_definable (d.roof j.val.1).graph_definable
      (hasPolynomialSignDescription_definable hX) (hasPolynomialSignDescription_definable hA) hx ha)
  have hR := hQE.finite_sign_description _
    ((d.tower k.val.1 k.val.2).slicedFiberPath_jointGraph_definable (d.roof k.val.1).graph_definable
      (hasPolynomialSignDescription_definable hB) (hasPolynomialSignDescription_definable hY) hb hy)
  exact jointUnitPathGraph_concat_semialgebraic hL (jointUnitPathGraph_concat_semialgebraic hG hR)

/-- A single directed edge, with actual endpoints and fixed-family budgets.
No joint charts, supplied selector or supplied germ are assumptions. The
ambient-format complete-chain theorem remains a separate obligation. -/
theorem published_cylindrical_directed_sliced_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] {n : ℕ} {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E))
    (j k : d.slicedLeaf) (P : Set (ρ → ℝ)) (x y : (ρ → ℝ) → Fin n → ℝ)
    (hPD : P ⊆ directedCellAttachmentDomain (d.slicedFiberCell j) (d.slicedFiberCell k))
    (hX : HasPolynomialSignDescription (selectedFunctionGraph P x))
    (hY : HasPolynomialSignDescription (selectedFunctionGraph P y))
    (hx : ∀ p ∈ P, x p ∈ projectionFiber (d.slicedFiberCell j) p)
    (hy : ∀ p ∈ P, y p ∈ projectionFiber (d.slicedFiberCell k) p) :
    ∃ (a : (ρ → ℝ) → Fin n → ℝ) (ε : (ρ → ℝ) → ℝ)
      (g : (ρ → ℝ) → ℝ → Fin n → ℝ) (sPath dPath : ℕ),
      HasPolynomialSignDescription (selectedFunctionGraph P a) ∧
      HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph P ε g) ∧
      HasPolynomialSignDescription (jointUnitPathGraph P (d.slicedAttachmentPath j k x y a ε g)) ∧
      (∀ p ∈ P, a p ∈ projectionFiber (d.slicedFiberCell j) p ∧
        a p ∈ closure (projectionFiber (d.slicedFiberCell k) p) ∧ 0 < ε p ∧ g p 0 = a p ∧
        ContinuousOn (g p) (Ico (0 : ℝ) (ε p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) (ε p)) (projectionFiber (d.slicedFiberCell k) p)) ∧
      ∀ p ∈ P, ∀ S : Set (Fin n → ℝ),
        projectionFiber (d.slicedFiberCell j) p ⊆ S → projectionFiber (d.slicedFiberCell k) p ⊆ S →
        ∃ γ : SemialgebraicUnitPath S (x p) (y p),
          γ.toFun = d.slicedAttachmentPath j k x y a ε g p ∧
          ∃ A : Finset (MvPolynomial (Unit ⊕ Fin n) ℝ), A.card ≤ sPath ∧
            (∀ q ∈ A, q.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  have hP := hQE.finite_sign_description P (selectedFunctionGraph_domain_definable P x
    (hasPolynomialSignDescription_definable hX))
  obtain ⟨a,ε,g,sG,dG,hA,hR,hG,hHalf,hB,h,hpaths⟩ :=
    published_cylindrical_joint_attachment_germ_paths hCAD hQE n P
      (d.slicedFiberCell j) (d.slicedFiberCell k) hP hPD
      (hQE.finite_sign_description _ (d.slicedFiberCell_definable j))
      (hQE.finite_sign_description _ (d.slicedFiberCell_definable k))
  have ha : ∀ p ∈ P, a p ∈ projectionFiber (d.slicedFiberCell j) p := fun p hp => (h p hp).1
  have hε : ∀ p ∈ P, 0 < ε p := fun p hp => (h p hp).2.2.1
  have hb : ∀ p ∈ P, g p (ε p/2) ∈ projectionFiber (d.slicedFiberCell k) p := by
    intro p hp
    exact (h p hp).2.2.2.2.2 ⟨half_pos (hε p hp),half_lt_self (hε p hp)⟩
  have hη := published_cylindrical_slicedAttachmentPath_semialgebraic
    hQE d j k x y a ε g hX hY hA hB hHalf hx hy ha hb
  obtain ⟨s,degree,hfmt⟩ := jointUnitPathGraph_uniform_fiber_format _ _ hη
  obtain ⟨sL,dL,hL⟩ := published_cylindrical_slicedFiberPath_bounded_unitPaths hQE
    (d.tower j.val.1 j.val.2) (d.roof j.val.1).graph_definable x a hX hA hx ha
  obtain ⟨sR,dR,hRight⟩ := published_cylindrical_slicedFiberPath_bounded_unitPaths hQE
    (d.tower k.val.1 k.val.2) (d.roof k.val.1).graph_definable
    (fun p => g p (ε p/2)) y hB hY hb hy
  refine ⟨a,ε,g,s,degree,hA,hR,hG,hη,h,?_⟩
  intro p hp S hCS hDS
  obtain ⟨γL,hγL,_⟩ := hL p hp
  obtain ⟨γR,hγR,_⟩ := hRight p hp
  obtain ⟨γG,hγG,_,_⟩ := hpaths p hp (ε p/2) (half_pos (hε p hp))
    (half_lt_self (hε p hp)) S hCS hDS
  let γ := (γL.weaken hCS).trans (γG.trans (γR.weaken hDS))
  have he : γ.toFun = d.slicedAttachmentPath j k x y a ε g p := by
    simp only [γ,CylindricalInitialBandDecomposition.slicedAttachmentPath,
      SemialgebraicUnitPath.trans_toFun,SemialgebraicUnitPath.weaken_toFun,hγL,hγR,hγG,
      jointHalfRadiusPath]
  obtain ⟨A,hs,hd,hsign⟩ := hfmt p hp
  exact ⟨γ,he,A,hs,hd,by simpa only [he] using hsign⟩

end PaperI
