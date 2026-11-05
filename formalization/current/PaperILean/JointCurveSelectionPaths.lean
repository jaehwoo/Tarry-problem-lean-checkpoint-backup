import PaperILean.JointCurveSelection
import PaperILean.CurveGermOriginalVariation

/-! Fixed-family format and the original analytic/sign variation estimates
for the newly constructed boundary germs. Bounds precede every parameter,
radius, ambient set and prescribed scalar function. Ambient source membership
is retained separately from fiberwise closure membership. -/

noncomputable section
namespace PaperI
open Set

theorem published_joint_curve_selection_bounded_paths
    (hChoice : PublishedSemialgebraicDefinableChoice)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ)) (a : (ρ → ℝ) → κ → ℝ)
    (hC : HasPolynomialSignDescription C)
    (ha : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hcl : ∀ p ∈ P, a p ∈ closure (projectionFiber C p)) :
    ∃ (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ) (sPath dPath : ℕ),
      HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph P ε g) ∧
      (∀ p ∈ P, 0 < ε p ∧ ε p < 1 ∧ g p 0 = a p ∧
        ContinuousOn (g p) (Ico (0 : ℝ) (ε p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) (ε p)) (projectionFiber C p)) ∧
      ∀ p ∈ P, ∀ r : ℝ, 0 < r → r < ε p → ∀ S : Set (κ → ℝ),
        a p ∈ S → projectionFiber C p ⊆ S →
        ∃ γ : SemialgebraicUnitPath S (a p) (g p r),
          γ.toFun = curveInitialSegment (g p) r ∧ g p r ∈ projectionFiber C p ∧
          ∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ), A.card ≤ sPath ∧
            (∀ q ∈ A, q.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨ε,g,hε,hG,hg⟩ := published_joint_curve_selection hChoice hQE hNash P C a hC ha hcl
  obtain ⟨sPath,dPath,hpath⟩ := published_curveGermFamily_initialSegment_paths hQE
    (jointCurveGermGraph P ε g) hG
  refine ⟨ε,g,sPath,dPath,hε,hG,hg,?_⟩
  intro p hp r hr hrε S haS hCS
  have h := hg p hp
  have hout := hpath p (ε p) r (g p) (projectionFiber C p) S
    (jointCurveGermGraph_fiber P ε g hp) hr hrε h.2.2.2.1 h.2.2.2.2
    (by simpa only [h.2.2.1] using haS) hCS
  obtain ⟨γ,hfun,hend,hformat⟩ := hout
  let γ' : SemialgebraicUnitPath S (a p) (g p r) :=
    { γ with source := γ.source.trans h.2.2.1 }
  exact ⟨γ',hfun,hend,hformat⟩

/-- The same generated family supports all subsequent scalar-function data.
The preserved Hardt input occurs in the inherited scalar-counting bridge,
not as a replacement for this boundary-curve construction. -/
theorem published_joint_curve_selection_original_variation
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
    ∃ (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ),
      HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph P ε g) ∧
      (∀ p ∈ P, 0 < ε p ∧ ε p < 1 ∧ g p 0 = a p ∧
        ContinuousOn (g p) (Ico (0 : ℝ) (ε p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) (ε p)) (projectionFiber C p)) ∧
      ∀ (ι : Type) [Fintype ι] (sF dF : ℕ), ∃ sPath dPath K M : ℕ,
      ∀ p ∈ P, ∀ r : ℝ, 0 < r → r < ε p → ∀ S : Set (κ → ℝ),
      a p ∈ S → projectionFiber C p ⊆ S →
      ∃ γ : SemialgebraicUnitPath S (a p) (g p r),
        γ.toFun = curveInitialSegment (g p) r ∧ g p r ∈ projectionFiber C p ∧
        (∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ), A.card ≤ sPath ∧
          (∀ q ∈ A, q.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun)) ∧
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
  obtain ⟨ε,g,hε,hG,hg⟩ := published_joint_curve_selection hChoice hQE hNash P C a hC ha hcl
  refine ⟨ε,g,hε,hG,hg,?_⟩
  intro ι _ sF dF
  obtain ⟨sPath,dPath,K,M,hvar⟩ := published_curveGermFamily_original_subdivision_variation
    hCell hHardt hQE hNash hPiece (jointCurveGermGraph P ε g) hG ι sF dF
  refine ⟨sPath,dPath,K,M,?_⟩
  intro p hp r hr hrε S haS hCS
  have h := hg p hp
  have hout := hvar p (ε p) r (g p) (projectionFiber C p) S
    (jointCurveGermGraph_fiber P ε g hp) hr hrε h.2.2.2.1 h.2.2.2.2
    (by simpa only [h.2.2.1] using haS) hCS
  obtain ⟨γ,hfun,hend,hformat,hvariation⟩ := hout
  let γ' : SemialgebraicUnitPath S (a p) (g p r) :=
    { γ with source := γ.source.trans h.2.2.1 }
  exact ⟨γ',hfun,hend,hformat,hvariation⟩

end PaperI
