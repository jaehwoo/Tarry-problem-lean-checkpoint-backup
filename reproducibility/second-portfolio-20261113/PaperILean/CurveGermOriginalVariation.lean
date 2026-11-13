import PaperILean.CurveGermSemialgebraic
import PaperILean.BoundedPathOriginalVariation

/-! Apply the preserved original analytic/sign subdivision to the actual
rescaled curve-germ path. For the fixed joint germ graph and fixed function
format, all bounds precede the fiber, radius, represented curve, cells,
ambient set, functions and range lengths. Existence of the joint germ family
is a distinct obligation; pointwise curve selection alone is not substituted.
No qualitative-monotonicity or path-connectedness contract is used. -/

noncomputable section
namespace PaperI
open Set

theorem published_curveGermFamily_original_subdivision_variation
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (G : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ)) (hG : HasPolynomialSignDescription G)
    (ι : Type) [Fintype ι] (sF dF : ℕ) :
    ∃ sPath dPath K M : ℕ, ∀ (p : ρ → ℝ) (ε r : ℝ) (g : ℝ → κ → ℝ)
      (C S : Set (κ → ℝ)),
      projectionFiber G p = curveGermGraph ε g → 0 < r → r < ε →
      ContinuousOn g (Ico (0 : ℝ) ε) → MapsTo g (Ioo (0 : ℝ) ε) C →
      g 0 ∈ S → C ⊆ S →
      ∃ γ : SemialgebraicUnitPath S (g 0) (g r),
        γ.toFun = curveInitialSegment g r ∧ g r ∈ C ∧
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
  obtain ⟨sPath,dPath,hPath⟩ := published_curveGermFamily_initialSegment_paths hQE G hG
  obtain ⟨K,M,hVar⟩ := published_bounded_unitPath_original_partition_variation
    hCell hHardt hQE hNash hPiece κ ι sPath dPath sF dF
  refine ⟨sPath,dPath,K,M,?_⟩
  intro p ε r g C S hgraph hr hrε hc hm h0 hCS
  obtain ⟨γ,hγ,hend,A,hcard,hdegree,hA⟩ :=
    hPath p ε r g C S hgraph hr hrε hc hm h0 hCS
  exact ⟨γ,hγ,hend,⟨A,hcard,hdegree,hA⟩,
    hVar S (g 0) (g r) γ A hcard hdegree hA⟩

end PaperI
