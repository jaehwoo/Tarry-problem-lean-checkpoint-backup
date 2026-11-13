import PaperILean.JointCurveSelectionPaths
import PaperILean.CurveGermFamilyOriginalVariation

/-! Reconcile the two checkpoint112 branches. The joint graph is constructed
by the parameter-compatible selection theorem. The explicit rescaling bounds
are then applied to this same graph. They depend on its sign format, not yet
only on the manuscript's original ambient input format. -/

noncomputable section
namespace PaperI
open Set

theorem jointCurveGermGraph_eq_halfOpenPathGraphFamily {ρ κ : Type*}
    (P : Set (ρ → ℝ)) (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ) :
    jointCurveGermGraph P ε g = halfOpenPathGraphFamily P ε g := rfl

theorem jointCurveGermGraph_fiber_offDomain {ρ κ : Type*}
    (P : Set (ρ → ℝ)) (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ)
    {p : ρ → ℝ} (hp : p ∉ P) :
    projectionFiber (jointCurveGermGraph P ε g) p = ∅ := by
  rw [jointCurveGermGraph_eq_halfOpenPathGraphFamily]
  exact halfOpenPathGraphFamily_fiber_offDomain P ε g hp

theorem jointCurveGermGraph_bounded_rescale_format {ρ κ : Type*}
    (P : Set (ρ → ℝ)) (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ)
    (A : Finset (MvPolynomial (ρ ⊕ (Unit ⊕ κ)) ℝ)) (s D : ℕ)
    (hcard : A.card ≤ s) (hdegree : ∀ q ∈ A, q.totalDegree ≤ D)
    (hG : PolynomialSignDetermined A (jointCurveGermGraph P ε g)) :
    ∀ p ∈ P, ∀ r : ℝ, 0 ≤ r → r < ε p →
      ∃ B : Finset (MvPolynomial (Unit ⊕ κ) ℝ), B.card ≤ s+2 ∧
        (∀ q ∈ B, q.totalDegree ≤ max (2*D) 1) ∧
        PolynomialSignDetermined B (unitPathGraph (curveInitialSegment (g p) r)) := by
  exact halfOpenPathGraphFamily_bounded_rescale_format P ε g A s D hcard hdegree hG

/-- Actual germs are constructed only over P; no closure or nonemptiness
condition is added outside the parameter domain. -/
theorem published_joint_curve_selection_germFamily
    (hChoice : PublishedSemialgebraicDefinableChoice)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ)) (a : (ρ → ℝ) → κ → ℝ)
    (hC : HasPolynomialSignDescription C)
    (ha : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hcl : ∀ p ∈ P, a p ∈ closure (projectionFiber C p)) :
    ∃ σ : ∀ p : P, SemialgebraicCurveGerm (projectionFiber C p.val) (a p.val),
      HasPolynomialSignDescription (curveGermFamilyGraph P (projectionFiber C) a σ) ∧
      ∀ p : P, (σ p).radius < 1 := by
  obtain ⟨ε,g,hε,⟨A,hA⟩,hg⟩ := published_joint_curve_selection hChoice hQE hNash P C a hC ha hcl
  let σ (p : P) : SemialgebraicCurveGerm (projectionFiber C p.val) (a p.val) :=
    { radius := ε p.val
      radius_pos := (hg p.val p.property).1
      toFun := g p.val
      continuousOn := (hg p.val p.property).2.2.2.1
      source := (hg p.val p.property).2.2.1
      enters := (hg p.val p.property).2.2.2.2
      semialgebraic := by
        have h := polynomialSignDetermined_projectionFiber p.val A (jointCurveGermGraph P ε g) hA
        rw [jointCurveGermGraph_fiber P ε g p.property,
          curveGermGraph_eq_halfOpenPathGraph] at h
        exact ⟨_,h⟩ }
  have heq : curveGermFamilyGraph P (projectionFiber C) a σ = jointCurveGermGraph P ε g := by
    ext v
    constructor
    · rintro ⟨hp,h⟩
      exact ⟨hp,h⟩
    · rintro ⟨hp,h⟩
      exact ⟨hp,h⟩
  refine ⟨σ,?_,fun p => (hg p.val p.property).2.1⟩
  rw [heq]
  exact ⟨A,hA⟩

theorem published_joint_curve_selection_explicit_format
    (hChoice : PublishedSemialgebraicDefinableChoice)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ)) (a : (ρ → ℝ) → κ → ℝ)
    (hC : HasPolynomialSignDescription C)
    (ha : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hcl : ∀ p ∈ P, a p ∈ closure (projectionFiber C p)) :
    ∃ (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ)
      (A : Finset (MvPolynomial (ρ ⊕ (Unit ⊕ κ)) ℝ)) (D : ℕ),
      HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)) ∧
      PolynomialSignDetermined A (jointCurveGermGraph P ε g) ∧
      (∀ q ∈ A, q.totalDegree ≤ D) ∧
      (∀ p ∈ P, 0 < ε p ∧ ε p < 1 ∧ g p 0 = a p ∧
        ContinuousOn (g p) (Ico (0 : ℝ) (ε p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) (ε p)) (projectionFiber C p)) ∧
      ∀ p ∈ P, ∀ r : ℝ, 0 < r → r < ε p → ∀ S : Set (κ → ℝ),
      a p ∈ S → projectionFiber C p ⊆ S →
      ∃ γ : SemialgebraicUnitPath S (a p) (g p r),
        γ.toFun = curveInitialSegment (g p) r ∧ g p r ∈ projectionFiber C p ∧
        ∃ B : Finset (MvPolynomial (Unit ⊕ κ) ℝ), B.card ≤ A.card+2 ∧
          (∀ q ∈ B, q.totalDegree ≤ max (2*D) 1) ∧
          PolynomialSignDetermined B (unitPathGraph γ.toFun) := by
  obtain ⟨ε,g,hε,⟨A,hA⟩,hg⟩ := published_joint_curve_selection hChoice hQE hNash P C a hC ha hcl
  let D := A.sup MvPolynomial.totalDegree
  have hD : ∀ q ∈ A, q.totalDegree ≤ D := fun q hq => Finset.le_sup hq
  refine ⟨ε,g,A,D,hε,hA,hD,hg,?_⟩
  intro p hp r hr hrε S haS hCS
  have h := hg p hp
  obtain ⟨B,hBc,hBd,hB⟩ := jointCurveGermGraph_bounded_rescale_format P ε g A A.card D
    le_rfl hD hA p hp r hr.le hrε
  let γ : SemialgebraicUnitPath S (a p) (g p r) :=
    { toFun := curveInitialSegment (g p) r
      continuousOn := curveInitialSegment_continuousOn h.2.2.2.1 hr.le hrε
      mapsTo := curveInitialSegment_mapsTo_ambient h.2.2.2.2 hr hrε
        (by simpa only [h.2.2.1] using haS) hCS
      source := (curveInitialSegment_source (g p) r).trans h.2.2.1
      target := curveInitialSegment_target (g p) r
      semialgebraic := ⟨B,hB⟩ }
  exact ⟨γ,rfl,h.2.2.2.2 ⟨hr,hrε⟩,B,hBc,hBd,hB⟩

theorem published_joint_curve_selection_explicit_original_variation
    (hChoice : PublishedSemialgebraicDefinableChoice)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hPiece : PublishedPiecewiseNashExtensions)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ)) (a : (ρ → ℝ) → κ → ℝ)
    (hC : HasPolynomialSignDescription C)
    (ha : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hcl : ∀ p ∈ P, a p ∈ closure (projectionFiber C p)) :
    ∃ (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ)
      (A : Finset (MvPolynomial (ρ ⊕ (Unit ⊕ κ)) ℝ)) (D : ℕ),
      HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)) ∧
      PolynomialSignDetermined A (jointCurveGermGraph P ε g) ∧
      (∀ q ∈ A, q.totalDegree ≤ D) ∧
      (∀ p ∈ P, 0 < ε p ∧ ε p < 1 ∧ g p 0 = a p ∧
        ContinuousOn (g p) (Ico (0 : ℝ) (ε p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) (ε p)) (projectionFiber C p)) ∧
      ∀ (ι : Type) [Fintype ι] (sF dF : ℕ), ∃ K M : ℕ,
      ∀ p ∈ P, ∀ r : ℝ, 0 < r → r < ε p → ∀ S : Set (κ → ℝ),
      a p ∈ S → projectionFiber C p ⊆ S →
      ∃ γ : SemialgebraicUnitPath S (a p) (g p r),
        γ.toFun = curveInitialSegment (g p) r ∧ g p r ∈ projectionFiber C p ∧
        (∃ B : Finset (MvPolynomial (Unit ⊕ κ) ℝ), B.card ≤ A.card+2 ∧
          (∀ q ∈ B, q.totalDegree ≤ max (2*D) 1) ∧ PolynomialSignDetermined B (unitPathGraph γ.toFun)) ∧
        ∀ (f : ι → (κ → ℝ) → ℝ) (B : ι → ℝ),
        (∀ i, ContinuousOn (f i) S) →
        (∀ i, ∃ A : Finset (MvPolynomial (κ ⊕ Unit) ℝ),
          A.card ≤ sF ∧ (∀ q ∈ A, q.totalDegree ≤ dF) ∧
            PolynomialSignDetermined A (scalarFunctionGraph S (f i))) →
        (∀ i, ∀ x ∈ S, ∀ y ∈ S, |f i x - f i y| ≤ B i) →
        ∃ cuts : Finset ℝ, 0 ∈ cuts ∧ 1 ∈ cuts ∧
          (∀ c ∈ cuts, c ∈ Icc (0 : ℝ) 1) ∧ cuts.card ≤ K ∧
          (∀ u ∈ cuts, ∀ v ∈ cuts, u < v → (∀ c ∈ cuts, c ∉ Ioo u v) →
            ∀ i, AnalyticOnNhd ℝ (fun t => f i (γ.toFun t)) (Ioo u v) ∧
              DerivativeSignOn (fun t => f i (γ.toFun t)) (Ioo u v)) ∧
        ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ M ∧ t 0 = 0 ∧ t n = 1 ∧
          MonotoneOn t (Icc 0 n) ∧
          (∀ j < n, ∀ i, MonotoneOn (fun u => f i (γ.toFun u)) (Ioo (t j) (t (j+1))) ∨
            AntitoneOn (fun u => f i (γ.toFun u)) (Ioo (t j) (t (j+1)))) ∧
          ∀ i, BoundedVariationOn (fun u => f i (γ.toFun u)) (Icc (0 : ℝ) 1) ∧
            variationOnFromTo (fun u => f i (γ.toFun u)) univ 0 1 ≤ (M : ℝ) * B i := by
  obtain ⟨ε,g,hε,⟨A,hA⟩,hg⟩ := published_joint_curve_selection hChoice hQE hNash P C a hC ha hcl
  let D := A.sup MvPolynomial.totalDegree
  have hD : ∀ q ∈ A, q.totalDegree ≤ D := fun q hq => Finset.le_sup hq
  refine ⟨ε,g,A,D,hε,hA,hD,hg,?_⟩
  intro ι _ sF dF
  obtain ⟨K,M,hVar⟩ := published_bounded_curveGermFamily_original_subdivision_variation
    hCell hHardt hQE hNash hPiece (ρ := ρ) (κ := κ) ι A.card D sF dF
  refine ⟨K,M,?_⟩
  intro p hp r hr hrε S haS hCS
  have h := hg p hp
  obtain ⟨γ,hfun,hend,hformat,hrest⟩ := hVar (jointCurveGermGraph P ε g) A
    le_rfl hD hA p (ε p) r (g p) (projectionFiber C p) S
    (jointCurveGermGraph_fiber P ε g hp) hr hrε h.2.2.2.1 h.2.2.2.2
    (by simpa only [h.2.2.1] using haS) hCS
  let γ' : SemialgebraicUnitPath S (a p) (g p r) :=
    { γ with source := γ.source.trans h.2.2.1 }
  exact ⟨γ',hfun,hend,hformat,hrest⟩

end PaperI
