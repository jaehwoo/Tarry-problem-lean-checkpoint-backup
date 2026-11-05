import PaperILean.CylindricalJointCurveSelection
import PaperILean.AllClosurePointGerms
import PaperILean.JointCurveSelectionFormat

/-! The constructed CAD germs, all fiber-closure points as parameters, and
strictly interior restrictions to the unit interval. Bounds precede every
parameter, closure point, cutoff and containing ambient set. -/

noncomputable section
namespace PaperI
open Set

theorem published_cylindrical_joint_curve_selection_bounded_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ)
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ Fin n) → ℝ)) (a : (ρ → ℝ) → Fin n → ℝ)
    (hC : HasPolynomialSignDescription C)
    (ha : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hcl : ∀ p ∈ P, a p ∈ closure (projectionFiber C p)) :
    ∃ (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → Fin n → ℝ) (sPath dPath : ℕ),
      HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph P ε g) ∧
      (∀ p ∈ P, 0 < ε p ∧ g p 0 = a p ∧
        ContinuousOn (g p) (Ico (0 : ℝ) (ε p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) (ε p)) (projectionFiber C p)) ∧
      ∀ p ∈ P, ∀ r : ℝ, 0 < r → r < ε p → ∀ S : Set (Fin n → ℝ),
        a p ∈ S → projectionFiber C p ⊆ S →
        ∃ γ : SemialgebraicUnitPath S (a p) (g p r),
          γ.toFun = curveInitialSegment (g p) r ∧ g p r ∈ projectionFiber C p ∧
          ∃ A : Finset (MvPolynomial (Unit ⊕ Fin n) ℝ), A.card ≤ sPath ∧
            (∀ q ∈ A, q.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨ε,g,hε,⟨A,hA⟩,hg⟩ := published_cylindrical_joint_curve_selection hCAD hQE n P C a hC ha hcl
  let D := A.sup MvPolynomial.totalDegree
  have hD : ∀ q ∈ A, q.totalDegree ≤ D := fun q hq => Finset.le_sup hq
  refine ⟨ε,g,A.card+2,max (2*D) 1,hε,⟨A,hA⟩,hg,?_⟩
  intro p hp r hr hrε S haS hCS
  have h := hg p hp
  obtain ⟨B,hBc,hBd,hB⟩ := jointCurveGermGraph_bounded_rescale_format P ε g A A.card D
    le_rfl hD hA p hp r hr.le hrε
  let γ : SemialgebraicUnitPath S (a p) (g p r) :=
    { toFun := curveInitialSegment (g p) r
      continuousOn := curveInitialSegment_continuousOn h.2.2.1 hr.le hrε
      mapsTo := curveInitialSegment_mapsTo_ambient h.2.2.2 hr hrε
        (by simpa only [h.2.1] using haS) hCS
      source := (curveInitialSegment_source (g p) r).trans h.2.1
      target := curveInitialSegment_target (g p) r
      semialgebraic := ⟨B,hB⟩ }
  exact ⟨γ,rfl,h.2.2.2 ⟨hr,hrε⟩,B,hBc,hBd,hB⟩

theorem published_cylindrical_all_closure_point_germs
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ)
    (C : Set ((ρ ⊕ Fin n) → ℝ)) (hC : HasPolynomialSignDescription C) :
    ∃ (ε : ((ρ ⊕ Fin n) → ℝ) → ℝ) (g : ((ρ ⊕ Fin n) → ℝ) → ℝ → Fin n → ℝ),
      HasPolynomialSignDescription
        (selectedFunctionGraph (fiberClosureRelation C) (fun q (_ : Unit) => ε q)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph (fiberClosureRelation C) ε g) ∧
      ∀ q ∈ fiberClosureRelation C,
        0 < ε q ∧ g q 0 = q ∘ Sum.inr ∧ ContinuousOn (g q) (Ico (0 : ℝ) (ε q)) ∧
        MapsTo (g q) (Ioo (0 : ℝ) (ε q)) (projectionFiber C (q ∘ Sum.inl)) := by
  have hCd := hasPolynomialSignDescription_definable hC
  have hP := fiberClosureRelation_definable hCd
  have hLift := hQE.finite_sign_description _ (closurePointLift_definable hCd)
  have ha := hQE.finite_sign_description _ (coordinateSectionGraph_definable hP Sum.inr)
  obtain ⟨ε,g,hε,hg,h⟩ := published_cylindrical_joint_curve_selection hCAD hQE n
    (fiberClosureRelation C) (closurePointLift C) (fun q => q ∘ Sum.inr) hLift ha
    (fun q hq => by simpa only [closurePointLift_fiber] using hq)
  exact ⟨ε,g,hε,hg,fun q hq => by simpa only [closurePointLift_fiber] using h q hq⟩

theorem published_cylindrical_all_closure_point_bounded_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ)
    (C : Set ((ρ ⊕ Fin n) → ℝ)) (hC : HasPolynomialSignDescription C) :
    ∃ (ε : ((ρ ⊕ Fin n) → ℝ) → ℝ) (g : ((ρ ⊕ Fin n) → ℝ) → ℝ → Fin n → ℝ)
      (sPath dPath : ℕ),
      HasPolynomialSignDescription
        (selectedFunctionGraph (fiberClosureRelation C) (fun q (_ : Unit) => ε q)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph (fiberClosureRelation C) ε g) ∧
      (∀ q ∈ fiberClosureRelation C,
        0 < ε q ∧ g q 0 = q ∘ Sum.inr ∧ ContinuousOn (g q) (Ico (0 : ℝ) (ε q)) ∧
        MapsTo (g q) (Ioo (0 : ℝ) (ε q)) (projectionFiber C (q ∘ Sum.inl))) ∧
      ∀ q ∈ fiberClosureRelation C, ∀ r : ℝ, 0 < r → r < ε q →
        ∀ S : Set (Fin n → ℝ), q ∘ Sum.inr ∈ S → projectionFiber C (q ∘ Sum.inl) ⊆ S →
        ∃ γ : SemialgebraicUnitPath S (q ∘ Sum.inr) (g q r),
          γ.toFun = curveInitialSegment (g q) r ∧ g q r ∈ projectionFiber C (q ∘ Sum.inl) ∧
          ∃ A : Finset (MvPolynomial (Unit ⊕ Fin n) ℝ), A.card ≤ sPath ∧
            (∀ v ∈ A, v.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  have hCd := hasPolynomialSignDescription_definable hC
  have hP := fiberClosureRelation_definable hCd
  have hLift := hQE.finite_sign_description _ (closurePointLift_definable hCd)
  have ha := hQE.finite_sign_description _ (coordinateSectionGraph_definable hP Sum.inr)
  obtain ⟨ε,g,s,d,hε,hg,h,hpath⟩ := published_cylindrical_joint_curve_selection_bounded_paths
    hCAD hQE n (fiberClosureRelation C) (closurePointLift C) (fun q => q ∘ Sum.inr)
    hLift ha (fun q hq => by simpa only [closurePointLift_fiber] using hq)
  refine ⟨ε,g,s,d,hε,hg,fun q hq => by simpa only [closurePointLift_fiber] using h q hq,?_⟩
  intro q hq r hr hre S haS hCS
  simpa only [closurePointLift_fiber] using hpath q hq r hr hre S haS
    (by simpa only [closurePointLift_fiber] using hCS)

theorem published_cylindrical_family_closure_path_format
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ)
    (C : Set ((ρ ⊕ Fin n) → ℝ)) (hC : HasPolynomialSignDescription C) :
    ∃ sPath dPath : ℕ, ∀ (p : ρ → ℝ) (a : Fin n → ℝ),
      a ∈ closure (projectionFiber C p) → ∀ S : Set (Fin n → ℝ),
      a ∈ S → projectionFiber C p ⊆ S →
      ∃ b ∈ projectionFiber C p, ∃ γ : SemialgebraicUnitPath S a b,
        ∃ A : Finset (MvPolynomial (Unit ⊕ Fin n) ℝ), A.card ≤ sPath ∧
          (∀ v ∈ A, v.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨ε,g,s,d,hε,hg,h,hpath⟩ := published_cylindrical_all_closure_point_bounded_paths hCAD hQE n C hC
  refine ⟨s,d,?_⟩
  intro p a ha S haS hCS
  let q := Sum.elim p a
  have hq : q ∈ fiberClosureRelation C := ha
  have hpos := (h q hq).1
  obtain ⟨γ,_,hend,hformat⟩ := hpath q hq (ε q/2) (half_pos hpos) (half_lt_self hpos)
    S haS hCS
  exact ⟨g q (ε q/2),hend,γ,hformat⟩

end PaperI
