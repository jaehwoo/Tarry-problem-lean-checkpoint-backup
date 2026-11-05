import PaperILean.FiberClosureRelation
import PaperILean.JointCurveSelectionPaths

/-! Treat every fiber-closure point as a real parameter before making joint
choices. The resulting bounds are uniform in the family parameter and source.
This supplies no parameterized cell decomposition or chart. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def closurePointLift {ρ κ : Type*} (C : Set ((ρ ⊕ κ) → ℝ)) :
    Set (((ρ ⊕ κ) ⊕ κ) → ℝ) :=
  {v | Sum.elim (fun i => v (Sum.inl (Sum.inl i))) (v ∘ Sum.inr) ∈ C}

theorem closurePointLift_fiber {ρ κ : Type*}
    (C : Set ((ρ ⊕ κ) → ℝ)) (q : (ρ ⊕ κ) → ℝ) :
    projectionFiber (closurePointLift C) q = projectionFiber C (q ∘ Sum.inl) := by
  ext x
  rfl

theorem closurePointLift_definable {ρ κ : Type} [Finite ρ] [Finite κ]
    {C : Set ((ρ ⊕ κ) → ℝ)} (hC : (univ : Set ℝ).Definable Language.ring C) :
    (univ : Set ℝ).Definable Language.ring (closurePointLift C) := by
  let e : ρ ⊕ κ → (ρ ⊕ κ) ⊕ κ := Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr
  convert hC.preimage_comp e using 1
  ext v
  have he : v ∘ e = Sum.elim (fun i => v (Sum.inl (Sum.inl i))) (v ∘ Sum.inr) := by
    funext i; cases i <;> rfl
  simp only [closurePointLift, mem_setOf_eq, mem_preimage, he]

theorem published_all_closure_point_germs
    (hChoice : PublishedSemialgebraicDefinableChoice)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (C : Set ((ρ ⊕ κ) → ℝ)) (hC : HasPolynomialSignDescription C) :
    ∃ (ε : ((ρ ⊕ κ) → ℝ) → ℝ) (g : ((ρ ⊕ κ) → ℝ) → ℝ → κ → ℝ),
      HasPolynomialSignDescription
        (selectedFunctionGraph (fiberClosureRelation C) (fun q (_ : Unit) => ε q)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph (fiberClosureRelation C) ε g) ∧
      ∀ q ∈ fiberClosureRelation C,
        0 < ε q ∧ ε q < 1 ∧ g q 0 = q ∘ Sum.inr ∧
        ContinuousOn (g q) (Ico (0 : ℝ) (ε q)) ∧
        MapsTo (g q) (Ioo (0 : ℝ) (ε q)) (projectionFiber C (q ∘ Sum.inl)) := by
  have hCd := hasPolynomialSignDescription_definable hC
  have hP := fiberClosureRelation_definable hCd
  have hLift := hQE.finite_sign_description _ (closurePointLift_definable hCd)
  have ha := hQE.finite_sign_description _ (coordinateSectionGraph_definable hP Sum.inr)
  obtain ⟨ε,g,hε,hg,h⟩ := published_joint_curve_selection hChoice hQE hNash
    (fiberClosureRelation C) (closurePointLift C) (fun q => q ∘ Sum.inr) hLift ha
    (fun q hq => by simpa only [closurePointLift_fiber] using hq)
  exact ⟨ε,g,hε,hg,fun q hq => by simpa only [closurePointLift_fiber] using h q hq⟩

theorem published_all_closure_point_bounded_paths
    (hChoice : PublishedSemialgebraicDefinableChoice)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (C : Set ((ρ ⊕ κ) → ℝ)) (hC : HasPolynomialSignDescription C) :
    ∃ (ε : ((ρ ⊕ κ) → ℝ) → ℝ) (g : ((ρ ⊕ κ) → ℝ) → ℝ → κ → ℝ)
      (sPath dPath : ℕ),
      HasPolynomialSignDescription
        (selectedFunctionGraph (fiberClosureRelation C) (fun q (_ : Unit) => ε q)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph (fiberClosureRelation C) ε g) ∧
      (∀ q ∈ fiberClosureRelation C,
        0 < ε q ∧ ε q < 1 ∧ g q 0 = q ∘ Sum.inr ∧
        ContinuousOn (g q) (Ico (0 : ℝ) (ε q)) ∧
        MapsTo (g q) (Ioo (0 : ℝ) (ε q)) (projectionFiber C (q ∘ Sum.inl))) ∧
      ∀ q ∈ fiberClosureRelation C, ∀ r : ℝ, 0 < r → r < ε q →
        ∀ S : Set (κ → ℝ), q ∘ Sum.inr ∈ S → projectionFiber C (q ∘ Sum.inl) ⊆ S →
        ∃ γ : SemialgebraicUnitPath S (q ∘ Sum.inr) (g q r),
          γ.toFun = curveInitialSegment (g q) r ∧ g q r ∈ projectionFiber C (q ∘ Sum.inl) ∧
          ∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ), A.card ≤ sPath ∧
            (∀ v ∈ A, v.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  have hCd := hasPolynomialSignDescription_definable hC
  have hP := fiberClosureRelation_definable hCd
  have hLift := hQE.finite_sign_description _ (closurePointLift_definable hCd)
  have ha := hQE.finite_sign_description _ (coordinateSectionGraph_definable hP Sum.inr)
  obtain ⟨ε,g,s,d,hε,hg,h,hpath⟩ := published_joint_curve_selection_bounded_paths
    hChoice hQE hNash (fiberClosureRelation C) (closurePointLift C) (fun q => q ∘ Sum.inr)
    hLift ha (fun q hq => by simpa only [closurePointLift_fiber] using hq)
  refine ⟨ε,g,s,d,hε,hg,fun q hq => by simpa only [closurePointLift_fiber] using h q hq,?_⟩
  intro q hq r hr hre S haS hCS
  simpa only [closurePointLift_fiber] using hpath q hq r hr hre S haS
    (by simpa only [closurePointLift_fiber] using hCS)

/-- Bounds precede the external parameter, the closure point and the ambient
set. A strictly interior half-radius, never the excluded radius, supplies b. -/
theorem published_family_closure_path_format
    (hChoice : PublishedSemialgebraicDefinableChoice)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (C : Set ((ρ ⊕ κ) → ℝ)) (hC : HasPolynomialSignDescription C) :
    ∃ sPath dPath : ℕ, ∀ (p : ρ → ℝ) (a : κ → ℝ),
      a ∈ closure (projectionFiber C p) → ∀ S : Set (κ → ℝ),
      a ∈ S → projectionFiber C p ⊆ S →
      ∃ b ∈ projectionFiber C p, ∃ γ : SemialgebraicUnitPath S a b,
        ∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ), A.card ≤ sPath ∧
          (∀ v ∈ A, v.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨ε,g,s,d,hε,hg,h,hpath⟩ := published_all_closure_point_bounded_paths hChoice hQE hNash C hC
  refine ⟨s,d,?_⟩
  intro p a ha S haS hCS
  let q := Sum.elim p a
  have hq : q ∈ fiberClosureRelation C := ha
  have hpos := (h q hq).1
  obtain ⟨γ,_,hend,hformat⟩ := hpath q hq (ε q/2) (half_pos hpos) (half_lt_self hpos)
    S haS hCS
  exact ⟨g q (ε q/2),hend,γ,hformat⟩

end PaperI
