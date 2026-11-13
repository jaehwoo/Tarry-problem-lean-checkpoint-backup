import PaperILean.CurveGermOriginalVariation
import PaperILean.CurveGermFamilyFormat

/-! Reconcile the two saved representations of the same actual germ graph,
then apply the original analytic/sign subdivision with format-only bounds.
The common old-time witness has Unit domain and is uniquely determined.
The input joint graph remains supplied; no pointwise choice is promoted to
a jointly semialgebraic family. Constants precede the graph, its coefficients,
every parameter and cutoff, the represented germs, ambient sets and functions.
Pre-strategy witness tests: evidence/germ_family112/original_variation_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set

theorem curveGermGraph_eq_halfOpenPathGraph {κ : Type*} (ε : ℝ) (g : ℝ → κ → ℝ) :
    curveGermGraph ε g = halfOpenPathGraph ε g := rfl

theorem rescaledGermRelation_eq_jointGermRescaledGraph {ρ κ : Type*}
    (G : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ)) :
    rescaledGermRelation G = jointGermRescaledGraph G := by
  ext v
  constructor
  · rintro ⟨ht,w,hw,hG⟩
    have he : w = fun _ => v (Sum.inl (Sum.inr ())) * v (Sum.inr (Sum.inl ())) := by
      funext u
      cases u
      exact hw
    rw [he] at hG
    exact ⟨ht,hG⟩
  · rintro ⟨ht,hG⟩
    exact ⟨ht,fun _ => v (Sum.inl (Sum.inr ())) * v (Sum.inr (Sum.inl ())),rfl,hG⟩

/-- The original subdivision applies uniformly to every supplied joint graph
of format (sG,dG). The explicit path format is (sG+2,max (2*dG) 1). No curve
selection or cell-chain existence conclusion is included in this statement. -/
theorem published_bounded_curveGermFamily_original_subdivision_variation
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (ι : Type) [Fintype ι] (sG dG sF dF : ℕ) :
    ∃ K M : ℕ, ∀ (G : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ))
      (A : Finset (MvPolynomial (ρ ⊕ (Unit ⊕ κ)) ℝ)),
      A.card ≤ sG → (∀ q ∈ A, q.totalDegree ≤ dG) → PolynomialSignDetermined A G →
      ∀ (p : ρ → ℝ) (ε r : ℝ) (g : ℝ → κ → ℝ) (C S : Set (κ → ℝ)),
      projectionFiber G p = curveGermGraph ε g → 0 < r → r < ε →
      ContinuousOn g (Ico (0 : ℝ) ε) → MapsTo g (Ioo (0 : ℝ) ε) C →
      g 0 ∈ S → C ⊆ S →
      ∃ γ : SemialgebraicUnitPath S (g 0) (g r),
        γ.toFun = curveInitialSegment g r ∧ g r ∈ C ∧
        (∃ B : Finset (MvPolynomial (Unit ⊕ κ) ℝ), B.card ≤ sG+2 ∧
          (∀ q ∈ B, q.totalDegree ≤ max (2*dG) 1) ∧
            PolynomialSignDetermined B (unitPathGraph γ.toFun)) ∧
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
  obtain ⟨K,M,hVar⟩ := published_bounded_unitPath_original_partition_variation
    hCell hHardt hQE hNash hPiece κ ι (sG+2) (max (2*dG) 1) sF dF
  refine ⟨K,M,?_⟩
  intro G A hAcard hAdegree hA p ε r g C S hgraph hr hrε hc hm h0 hCS
  obtain ⟨B,hBcard,hBdegree,hB⟩ := jointGermRescaledGraph_bounded_fiber_format
    A G sG dG hAcard hAdegree hA p r
  rw [← rescaledGermRelation_eq_jointGermRescaledGraph,
    rescaledGermRelation_fiber G p ε r g hgraph hr.le hrε] at hB
  let γ : SemialgebraicUnitPath S (g 0) (g r) :=
    { toFun := curveInitialSegment g r
      continuousOn := curveInitialSegment_continuousOn hc hr.le hrε
      mapsTo := curveInitialSegment_mapsTo_ambient hm hr hrε h0 hCS
      source := curveInitialSegment_source g r
      target := curveInitialSegment_target g r
      semialgebraic := ⟨B,hB⟩ }
  exact ⟨γ,rfl,hm ⟨hr,hrε⟩,⟨B,hBcard,hBdegree,hB⟩,
    hVar S (g 0) (g r) γ B hBcard hBdegree hB⟩

end PaperI
