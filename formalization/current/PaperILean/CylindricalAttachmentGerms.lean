import PaperILean.CylindricalDefinableChoice
import PaperILean.CylindricalClosurePaths
import PaperILean.JointAttachmentPaths

/-! Actual-cell / other-fiber-closure attachment selection and paths using the
constructed CAD selector and CAD germs. Generic choice, Nash regularity and
Hardt are not external premises of these theorems. -/

noncomputable section
namespace PaperI
open Set

theorem published_cylindrical_joint_attachment_selector
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (C D : Set ((ρ ⊕ κ) → ℝ))
    (hC : HasPolynomialSignDescription C) (hD : HasPolynomialSignDescription D) :
    ∃ a : (ρ → ℝ) → κ → ℝ,
      HasPolynomialSignDescription (selectedFunctionGraph (directedCellAttachmentDomain C D) a) ∧
      ∀ p ∈ directedCellAttachmentDomain C D,
        a p ∈ projectionFiber C p ∧ a p ∈ closure (projectionFiber D p) :=
  published_joint_attachment_selector (hCAD.toDefinableChoice hQE) hQE C D hC hD

theorem published_cylindrical_joint_attachment_selector_on
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (P : Set (ρ → ℝ)) (C D : Set ((ρ ⊕ κ) → ℝ))
    (hP : HasPolynomialSignDescription P) (hPD : P ⊆ directedCellAttachmentDomain C D)
    (hC : HasPolynomialSignDescription C) (hD : HasPolynomialSignDescription D) :
    ∃ a : (ρ → ℝ) → κ → ℝ,
      HasPolynomialSignDescription (selectedFunctionGraph P a) ∧
      ∀ p ∈ P, a p ∈ projectionFiber C p ∧ a p ∈ closure (projectionFiber D p) :=
  published_joint_attachment_selector_on (hCAD.toDefinableChoice hQE) hQE P C D hP hPD hC hD

/-- The budget precedes the parameter, every strictly interior cutoff, and the
containing ambient set. It may depend on the fixed joint relations P,C,D. -/
theorem published_cylindrical_joint_attachment_germ_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ)
    (P : Set (ρ → ℝ)) (C D : Set ((ρ ⊕ Fin n) → ℝ))
    (hP : HasPolynomialSignDescription P) (hPD : P ⊆ directedCellAttachmentDomain C D)
    (hC : HasPolynomialSignDescription C) (hD : HasPolynomialSignDescription D) :
    ∃ (a : (ρ → ℝ) → Fin n → ℝ) (ε : (ρ → ℝ) → ℝ)
      (g : (ρ → ℝ) → ℝ → Fin n → ℝ) (sPath dPath : ℕ),
      HasPolynomialSignDescription (selectedFunctionGraph P a) ∧
      HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph P ε g) ∧
      HasPolynomialSignDescription (jointUnitPathGraph P (jointHalfRadiusPath ε g)) ∧
      HasPolynomialSignDescription (selectedFunctionGraph P (fun p => g p (ε p/2))) ∧
      (∀ p ∈ P, a p ∈ projectionFiber C p ∧ a p ∈ closure (projectionFiber D p) ∧
        0 < ε p ∧ g p 0 = a p ∧ ContinuousOn (g p) (Ico (0 : ℝ) (ε p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) (ε p)) (projectionFiber D p)) ∧
      ∀ p ∈ P, ∀ r : ℝ, 0 < r → r < ε p → ∀ S : Set (Fin n → ℝ),
        projectionFiber C p ⊆ S → projectionFiber D p ⊆ S →
        ∃ γ : SemialgebraicUnitPath S (a p) (g p r),
          γ.toFun = curveInitialSegment (g p) r ∧ g p r ∈ projectionFiber D p ∧
          ∃ A : Finset (MvPolynomial (Unit ⊕ Fin n) ℝ), A.card ≤ sPath ∧
            (∀ q ∈ A, q.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨a,hA,ha⟩ := published_cylindrical_joint_attachment_selector_on hCAD hQE P C D hP hPD hC hD
  obtain ⟨ε,g,s,d,hR,hG,h,hpath⟩ := published_cylindrical_joint_curve_selection_bounded_paths
    hCAD hQE n P D a hD hA (fun p hp => (ha p hp).2)
  have hε : ∀ p ∈ P, 0 < ε p := fun p hp => (h p hp).1
  refine ⟨a,ε,g,s,d,hA,hR,hG,
    published_jointHalfRadiusPath_semialgebraic hQE P ε g hε hR hG,
    published_jointHalfRadiusEndpoint_semialgebraic hQE P ε g hε hR hG,
    fun p hp => ⟨(ha p hp).1,(ha p hp).2,h p hp⟩,?_⟩
  intro p hp r hr hre S hCS hDS
  exact hpath p hp r hr hre S (hCS (ha p hp).1) hDS

end PaperI
