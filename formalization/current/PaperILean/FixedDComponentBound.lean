import PaperILean.FixedDBodyControl
import PaperILean.SectionIntegralReadouts
import PaperILean.OriginalHaarWindowComponentPaths
import PaperILean.OriginalHaarWindowPieces
import PaperILean.OriginalGaussRelativeFrameIntegration
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Actual fixed-d augmented component paths for I3237.
The body estimate is proved from the actual five-column singular bound.
Existing analytic endpoint and ordered gluing estimates are reused unchanged. -/
noncomputable section
namespace PaperI.FixedDComponentBound
open Set Filter
open scoped BigOperators Topology
open RegularSectionDifferential RegularSectionRates FixedDBodyControl

/-- One actual analytic piece, allowing singular derivatives at its endpoints.
Every augmented physical coordinate is included in the readout family. -/
theorem fixed_d_actual_analytic_piece_bound
    {k : ℕ} (S0 : AugmentedState k) (E : Set (Fin 6 → ℝ))
    (d0 P Cs Cw : ℝ) (hP : 0 < P)
    (hfixed : ∀ x ∈ E, x 3 = d0)
    (hwindow : ∀ x ∈ E, augmentedStateNorm (augmentedPullback S0 x) ≤ P^Cw)
    (hpivot : ∀ x ∈ E, P^(-Cs) ≤ descendingSingularValues
      (dComplement (augmentedPullback S0 x)) (Fin.last 4))
    (g : ℝ → Fin 6 → ℝ) (hgc : ContinuousOn g (Icc (0:ℝ) 1))
    (hgE : ∀ t ∈ Icc (0:ℝ) 1, g t ∈ E)
    (u v : ℝ) (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1) (huv : u < v)
    (hgan : ∀ i : Fin 6, AnalyticOnNhd ℝ (fun t => g t i) (Ioo u v))
    (hqan : ∀ i : AugmentedCoordinateIndex k,
      AnalyticOnNhd ℝ (fun t => augmentedStateCoordinates k
        (augmentedPullback S0 (g t)) i) (Ioo u v))
    (hqsign : ∀ i : AugmentedCoordinateIndex k,
      DerivativeSignOn (fun t => augmentedStateCoordinates k
        (augmentedPullback S0 (g t)) i) (Ioo u v)) :
    let L : ℝ := P^Cs * (Fintype.card (AugmentedCoordinateIndex k):ℝ) * (2*P^Cw)
    ‖originalUpperRelativeFrame (g u) (g v)‖ ≤ L*(1+L)^2 := by
  let q : AugmentedCoordinateIndex k → ℝ → ℝ := fun i t =>
    augmentedStateCoordinates k (augmentedPullback S0 (g t)) i
  let dq : AugmentedCoordinateIndex k → ℝ → ℝ := fun i => deriv (q i)
  let b : ℝ → Fin 6 → ℝ := fun t => originalAffineBodyCoordinates (g t) (deriv g t)
  have hsub : Icc u v ⊆ Icc (0:ℝ) 1 :=
    fun t ht => ⟨hu.1.trans ht.1,ht.2.trans hv.2⟩
  have hga : AnalyticOnNhd ℝ g (Ioo u v) := AnalyticOnNhd.pi hgan
  have hgd (t : ℝ) (ht : t ∈ Ioo u v) : HasDerivAt g (deriv g t) t :=
    (hga t ht).differentiableAt.hasDerivAt
  have hqd (i : AugmentedCoordinateIndex k) (t : ℝ) (ht : t ∈ Ioo u v) :
      HasDerivAt (q i) (dq i t) t := (hqan i t ht).differentiableAt.hasDerivAt
  apply originalHaar_analytic_piece_relative_bound g b q dq u v (P^Cw) (P^Cs)
    huv (Real.rpow_nonneg hP.le _) (Real.rpow_nonneg hP.le _) (hgc.mono hsub)
  · exact originalAffineBodyCoordinates_continuousOn g (deriv g) _
      hga.continuousOn hga.deriv.continuousOn
  · intro t ht
    simpa only [b,originalUpperBodyVelocity_body] using hgd t ht
  · exact hqd
  · intro i
    exact (hqan i).deriv.continuousOn
  · exact hqsign
  · intro i t ht
    exact (abs_le_sqrt_sum_sq
      (augmentedStateCoordinates k (augmentedPullback S0 (g t))) i).trans
        (hwindow _ (hgE t (hsub ⟨ht.1.le,ht.2.le⟩)))
  · intro t ht i
    have hdLocal : ∀ᶠ r in 𝓝 t, g r 3 = d0 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      exact hfixed _ (hgE r (hsub ⟨hr.1.le,hr.2.le⟩))
    exact fixed_d_body_majorant S0 g (deriv g t) t d0 P Cs hP (hgd t ht)
      hdLocal (hpivot _ (hgE t (hsub ⟨ht.1.le,ht.2.le⟩))) i

/-- The cut exponent precedes every seed, polynomial coefficient, scale,
fixed fiber level and endpoint pair. The path and its actual body majorant
are constructed, not assumed. No global C1 or absolute-coordinate bound occurs. -/
theorem fixed_d_component_relative_bound
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) :
    ∃ M : ℕ, ∀ (P Cs Cw : ℝ) (S0 : AugmentedState k)
      (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ)) (d0 : ℝ),
      2 ≤ P → A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A E →
      (∀ x ∈ E, x 3 = d0) →
      (∀ x ∈ E, augmentedStateNorm (augmentedPullback S0 x) ≤ P^Cw) →
      (∀ x ∈ E, P^(-Cs) ≤ descendingSingularValues
        (dComplement (augmentedPullback S0 x)) (Fin.last 4)) →
      ∀ z a b : Fin 6 → ℝ, a ∈ connectedComponentIn E z → b ∈ connectedComponentIn E z →
        let L : ℝ := P^Cs * (Fintype.card (AugmentedCoordinateIndex k):ℝ) * (2*P^Cw)
        ‖originalUpperRelativeFrame a b‖+1 ≤ (1+2*L*(1+L)^2)^M := by
  classical
  obtain ⟨N,M,hPaths⟩ := published_originalHaar_component_polynomial_paths
    hCell hPath hHardt hQE hNash hPiece (Fin 6) (AugmentedCoordinateIndex k)
    s D (max k 1)
  refine ⟨M,?_⟩
  intro P Cs Cw S0 A E d0 hP hAc hAd hAE hfixed hwindow hpivot z a b ha hb
  dsimp only
  have hPpos : 0 < P := by linarith
  let L : ℝ := P^Cs * (Fintype.card (AugmentedCoordinateIndex k):ℝ) * (2*P^Cw)
  let R : ℝ := L*(1+L)^2
  have hR : 0 ≤ R := by dsimp [R,L]; positivity
  have hp := hPaths A E hAc hAd hAE
  obtain ⟨γ,C,hC0,hC1,hCI,hCM,hCprops⟩ := hp.2.2
    (SectionIntegralReadouts.augmentedPolynomial S0)
    (SectionIntegralReadouts.augmentedPolynomial_degree S0) z a b ha hb
  obtain ⟨n,t,hnC,ht0,htn,htmono,htgap⟩ := exists_sorted_cut_partition C hC0 hC1 hCI
  have hnM : n ≤ M := by omega
  have hgE : ∀ r ∈ Icc (0:ℝ) 1, γ.toFun r ∈ E := by
    intro r hr
    exact (connectedComponentIn_subset E z) (γ.mapsTo hr)
  have hstep : ∀ j<n,
      ‖originalUpperRelativeFrame (γ.toFun (t j)) (γ.toFun (t (j+1)))‖ ≤ R := by
    intro j hj
    obtain ⟨hu,hv,huv,hgap⟩ := htgap j hj
    have hprops := hCprops (t j) hu (t (j+1)) hv huv hgap
    apply fixed_d_actual_analytic_piece_bound S0 E d0 P Cs Cw hPpos hfixed hwindow hpivot
      γ.toFun γ.continuousOn hgE (t j) (t (j+1)) (hCI _ hu) (hCI _ hv) huv hprops.1
    · intro i
      simpa only [SectionIntegralReadouts.augmentedPolynomial_eval] using (hprops.2 i).1
    · intro i
      simpa only [SectionIntegralReadouts.augmentedPolynomial_eval] using (hprops.2 i).2
  have hc := originalUpperRelativeFrame_chain_bound (fun j => γ.toFun (t j)) n R hR hstep
  dsimp only at hc
  rw [ht0,htn,γ.source,γ.target] at hc
  simpa only [R,L,mul_assoc] using
    hc.trans (pow_le_pow_right₀ (by linarith : 1 ≤ 1+2*R) hnM)

end PaperI.FixedDComponentBound
