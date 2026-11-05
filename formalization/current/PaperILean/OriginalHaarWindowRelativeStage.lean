import PaperILean.OriginalHaarWindowActualPath

/-! The complete original coefficient-variation/body/relative-frame stage
I2333-I2337 for the actual normalized orbit and every original subgroup.
Only the original norm/pivot hypotheses and named accepted published inputs
remain. The final Haar-measure and arbitrary-polynomial passages are separate. -/
noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Uniform component-relative coordinate control on the actual orbit window.
No absolute frame bound, supplied derivative, supplied path, desired box bound,
incidence statement, or main-theorem premise is assumed. -/
theorem originalHaarOrbitWindow_relative_stage
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) :
    ∃ N M : ℕ, ∀ (K : OriginalHaarSubgroup) (F : CoefficientSpace k)
      (A : Finset (MvPolynomial (MonomialIndex k) ℝ)) (W : Set (CoefficientSpace k)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A W →
      ∀ B H : ℝ, 0 ≤ B → 0 ≤ H →
      (∀ J ∈ W, coefficientEuclideanNorm J ≤ B) →
      (∀ J ∈ W, ∀ v ∈ originalHaarSubgroupSet K,
        coordinateL2Norm v ≤ H*coefficientEuclideanNorm (originalHaarPhysicalLieAction J v)) →
      let E := originalHaarOrbitWindow K F W
      let L : ℝ := H*(Fintype.card (MonomialIndex k):ℝ)*(2*B)
      let R : ℝ := L*(1+L)^2
      Finite (ConnectedComponents E) ∧ Nat.card (ConnectedComponents E) ≤ N ∧
      ∀ z a b : Fin 6 → ℝ, a ∈ connectedComponentIn E z → b ∈ connectedComponentIn E z →
        ‖originalUpperRelativeFrame a b‖+1 ≤ (1+2*R)^M := by
  obtain ⟨N,M,hPaths⟩ := published_originalHaar_component_polynomial_paths
    hCell hPath hHardt hQE hNash hPiece (Fin 6) (MonomialIndex k)
    (s+6) (max (D*k) 1) k
  refine ⟨N,M,?_⟩
  intro K F A W hAc hAd hAW B H hB hH hWnorm hWpiv
  dsimp only
  let E := originalHaarOrbitWindow K F W
  let L : ℝ := H*(Fintype.card (MonomialIndex k):ℝ)*(2*B)
  let R : ℝ := L*(1+L)^2
  have hR : 0 ≤ R := by dsimp [R,L]; positivity
  obtain ⟨AE,hAEc,hAEd,hAES⟩ := originalHaarOrbitWindow_bounded_sign_format K F A W s D hAc hAd hAW
  have hp := hPaths AE E hAEc hAEd hAES
  refine ⟨hp.1,hp.2.1,?_⟩
  intro z a b ha hb
  obtain ⟨γ,C,hC0,hC1,hCI,hCM,hCprops⟩ := hp.2.2
    (OriginalHaarOrbitPolynomial.orbitPolynomial F)
    (OriginalHaarOrbitPolynomial.orbitPolynomial_degree F) z a b ha hb
  obtain ⟨n,t,hnC,ht0,htn,htmono,htgap⟩ := exists_sorted_cut_partition C hC0 hC1 hCI
  have hnM : n ≤ M := by omega
  have hgW : ∀ r ∈ Icc (0:ℝ) 1, γ.toFun r ∈ originalHaarOrbitWindow K F W := by
    intro r hr
    exact (connectedComponentIn_subset E z) (γ.mapsTo hr)
  have hstep : ∀ j<n,
      ‖originalUpperRelativeFrame (γ.toFun (t j)) (γ.toFun (t (j+1)))‖ ≤ R := by
    intro j hj
    obtain ⟨hu,hv,huv,hgap⟩ := htgap j hj
    have hprops := hCprops (t j) hu (t (j+1)) hv huv hgap
    apply originalHaar_actual_analytic_piece_bound K F W B H hB hH hWnorm hWpiv
      γ.toFun γ.continuousOn hgW (t j) (t (j+1)) (hCI _ hu) (hCI _ hv) huv hprops.1
    · intro α
      simpa only [OriginalHaarOrbitPolynomial.orbitPolynomial_eval] using (hprops.2 α).1
    · intro α
      simpa only [OriginalHaarOrbitPolynomial.orbitPolynomial_eval] using (hprops.2 α).2
  have hc := originalUpperRelativeFrame_chain_bound (fun j => γ.toFun (t j)) n R hR hstep
  dsimp only at hc
  rw [ht0,htn,γ.source,γ.target] at hc
  exact hc.trans (pow_le_pow_right₀ (by linarith : 1 ≤ 1+2*R) hnM)

end PaperI
