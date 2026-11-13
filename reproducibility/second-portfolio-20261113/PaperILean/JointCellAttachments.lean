import PaperILean.FiberClosureRelation
import PaperILean.JointCurveSelectionPaths
import PaperILean.FiniteClosureAttachment

/-! Admissible attachment domains and jointly selected source points.
The witness is in an actual source cell and the target cell's fiberwise
closure. Both cells must lie in the ambient set used for the germ path.
No parameterized cell decomposition or jointly selected chain is assumed. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def directedCellAttachment {ρ κ : Type*} (C D : Set ((ρ ⊕ κ) → ℝ)) :
    Set ((ρ ⊕ κ) → ℝ) := C ∩ fiberClosureRelation D

def directedCellAttachmentDomain {ρ κ : Type*} (C D : Set ((ρ ⊕ κ) → ℝ)) :
    Set (ρ → ℝ) := projectionDomain (directedCellAttachment C D)

theorem directedCellAttachment_fiber {ρ κ : Type*}
    (C D : Set ((ρ ⊕ κ) → ℝ)) (p : ρ → ℝ) :
    projectionFiber (directedCellAttachment C D) p =
      projectionFiber C p ∩ closure (projectionFiber D p) := by
  ext a
  rfl

theorem mem_directedCellAttachmentDomain_iff {ρ κ : Type*}
    (C D : Set ((ρ ⊕ κ) → ℝ)) (p : ρ → ℝ) :
    p ∈ directedCellAttachmentDomain C D ↔
      (projectionFiber C p ∩ closure (projectionFiber D p)).Nonempty := Iff.rfl

theorem directedCellAttachment_definable {ρ κ : Type} [Finite ρ] [Fintype κ]
    {C D : Set ((ρ ⊕ κ) → ℝ)}
    (hC : (univ : Set ℝ).Definable Language.ring C)
    (hD : (univ : Set ℝ).Definable Language.ring D) :
    (univ : Set ℝ).Definable Language.ring (directedCellAttachment C D) :=
  hC.inter (fiberClosureRelation_definable hD)

theorem directedCellAttachmentDomain_definable {ρ κ : Type} [Finite ρ] [Fintype κ]
    {C D : Set ((ρ ⊕ κ) → ℝ)}
    (hC : (univ : Set ℝ).Definable Language.ring C)
    (hD : (univ : Set ℝ).Definable Language.ring D) :
    (univ : Set ℝ).Definable Language.ring (directedCellAttachmentDomain C D) :=
  realDefinable_exists (directedCellAttachment_definable hC hD)

theorem published_joint_attachment_selector
    (hChoice : PublishedSemialgebraicDefinableChoice) (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (C D : Set ((ρ ⊕ κ) → ℝ))
    (hC : HasPolynomialSignDescription C) (hD : HasPolynomialSignDescription D) :
    ∃ a : (ρ → ℝ) → κ → ℝ,
      HasPolynomialSignDescription (selectedFunctionGraph (directedCellAttachmentDomain C D) a) ∧
      ∀ p ∈ directedCellAttachmentDomain C D,
        a p ∈ projectionFiber C p ∧ a p ∈ closure (projectionFiber D p) := by
  obtain ⟨a,ha,hm⟩ := hChoice.section_exists (directedCellAttachment C D)
    (hQE.finite_sign_description _ (directedCellAttachment_definable
      (hasPolynomialSignDescription_definable hC) (hasPolynomialSignDescription_definable hD)))
  exact ⟨a,ha,hm⟩

def cellAdjacencyParameterDomain {ρ κ : Type*} (C D : Set ((ρ ⊕ κ) → ℝ)) :
    Set (ρ → ℝ) := directedCellAttachmentDomain C D ∪ directedCellAttachmentDomain D C

theorem cellAdjacencyParameterDomain_definable {ρ κ : Type} [Finite ρ] [Fintype κ]
    {C D : Set ((ρ ⊕ κ) → ℝ)}
    (hC : (univ : Set ℝ).Definable Language.ring C)
    (hD : (univ : Set ℝ).Definable Language.ring D) :
    (univ : Set ℝ).Definable Language.ring (cellAdjacencyParameterDomain C D) :=
  (directedCellAttachmentDomain_definable hC hD).union
    (directedCellAttachmentDomain_definable hD hC)

theorem cellAdjacencyParameterDomain_iff_adj {ρ κ ι : Type*}
    (C : ι → Set ((ρ ⊕ κ) → ℝ)) (p : ρ → ℝ) {i j : ι} (hij : i ≠ j) :
    p ∈ cellAdjacencyParameterDomain (C i) (C j) ↔
      (closureAttachmentGraph (fun k => projectionFiber (C k) p)).Adj i j := by
  change (_ ∨ _) ↔ i ≠ j ∧ (_ ∨ _)
  exact (and_iff_right hij).symm

/-- The source, positive radius and curve are all selected jointly. Fixed-family
path budgets precede every parameter, cutoff and containing ambient set. -/
theorem published_joint_attachment_germ_paths
    (hChoice : PublishedSemialgebraicDefinableChoice)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (C D : Set ((ρ ⊕ κ) → ℝ))
    (hC : HasPolynomialSignDescription C) (hD : HasPolynomialSignDescription D) :
    ∃ (a : (ρ → ℝ) → κ → ℝ) (ε : (ρ → ℝ) → ℝ)
      (g : (ρ → ℝ) → ℝ → κ → ℝ) (sPath dPath : ℕ),
      HasPolynomialSignDescription (selectedFunctionGraph (directedCellAttachmentDomain C D) a) ∧
      HasPolynomialSignDescription
        (selectedFunctionGraph (directedCellAttachmentDomain C D) (fun p (_ : Unit) => ε p)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph (directedCellAttachmentDomain C D) ε g) ∧
      (∀ p ∈ directedCellAttachmentDomain C D,
        a p ∈ projectionFiber C p ∧ a p ∈ closure (projectionFiber D p) ∧
        0 < ε p ∧ ε p < 1 ∧ g p 0 = a p ∧
        ContinuousOn (g p) (Ico (0 : ℝ) (ε p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) (ε p)) (projectionFiber D p)) ∧
      ∀ p ∈ directedCellAttachmentDomain C D, ∀ r : ℝ, 0 < r → r < ε p →
        ∀ S : Set (κ → ℝ), projectionFiber C p ⊆ S → projectionFiber D p ⊆ S →
        ∃ γ : SemialgebraicUnitPath S (a p) (g p r),
          γ.toFun = curveInitialSegment (g p) r ∧ g p r ∈ projectionFiber D p ∧
          ∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ), A.card ≤ sPath ∧
            (∀ v ∈ A, v.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨a,ha,hm⟩ := published_joint_attachment_selector hChoice hQE C D hC hD
  obtain ⟨ε,g,s,d,hε,hg,h,hpath⟩ := published_joint_curve_selection_bounded_paths
    hChoice hQE hNash (directedCellAttachmentDomain C D) D a hD ha
    (fun p hp => (hm p hp).2)
  refine ⟨a,ε,g,s,d,ha,hε,hg,fun p hp => ⟨(hm p hp).1,(hm p hp).2,h p hp⟩,?_⟩
  intro p hp r hr hre S hCS hDS
  exact hpath p hp r hr hre S (hCS (hm p hp).1) hDS

end PaperI
