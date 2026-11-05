import PaperILean.OriginalHaarWindowScale

/-! The literal polynomial-in-P conclusion for the source coefficient and
inverse physical-pivot bounds P^C. The original exponent C can be any real;
constants are uniform in phases, window coefficients and group locations. -/
noncomputable section
namespace PaperI
open Set
open OriginalHaarWindowMeasures
open scoped ENNReal

/-- The bounded-degree quotient version of the source Haar estimate with its
actual real powers and the original global convention P>=2. -/
theorem originalHaarOrbitWindow_power_bound
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) :
    ∃ A0 : ℝ, 1 ≤ A0 ∧ ∀ c : ℝ, ∃ b : ℝ, 0 ≤ b ∧
      ∀ (K : OriginalHaarSubgroup) (F : CoefficientSpace k)
        (A : Finset (MvPolynomial (MonomialIndex k) ℝ)) (W : Set (CoefficientSpace k)),
        A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A W →
        ∀ P : ℝ, 2 ≤ P →
        (∀ J ∈ W, coefficientEuclideanNorm J ≤ P^c) →
        (∀ J ∈ W, ∀ v ∈ originalHaarSubgroupSet K,
          coordinateL2Norm v ≤ P^c*coefficientEuclideanNorm (originalHaarPhysicalLieAction J v)) →
        subgroupHaar K (originalHaarOrbitWindow K F W) ≤ ENNReal.ofReal (A0*P^b) := by
  obtain ⟨N,M,hvol⟩ := originalHaarOrbitWindow_scaled_volume_stage
    hCell hPath hHardt hQE hNash hPiece k s D
  let C : ℝ := 1+4*(Fintype.card (MonomialIndex k):ℝ)*
    (1+2*(Fintype.card (MonomialIndex k):ℝ))^2
  let A0 : ℝ := 1+(N:ℝ)*(2*C^M)^4
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hA0 : 1 ≤ A0 := by
    have hn : 0 ≤ (N:ℝ)*(2*C^M)^4 := by positivity
    dsimp [A0]
    linarith
  have hAnn : (N:ℝ≥0∞)*ENNReal.ofReal (2*C^M)^4 ≤ ENNReal.ofReal A0 := by
    have he : ENNReal.ofReal ((N:ℝ)*(2*C^M)^4) =
        (N:ℝ≥0∞)*ENNReal.ofReal (2*C^M)^4 := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (N:ℝ)),ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (by positivity : 0 ≤ 2*C^M) 4]
    rw [← he]
    exact ENNReal.ofReal_le_ofReal (by dsimp [A0]; linarith)
  refine ⟨A0,hA0,?_⟩
  intro c
  let b : ℝ := max c 0*(24*M:ℕ)
  have hb : 0 ≤ b := mul_nonneg (le_max_right _ _) (by positivity)
  refine ⟨b,hb,?_⟩
  intro K F A W hAc hAd hAW P hP hWnorm hWpiv
  have hP1 : 1 ≤ P := by linarith
  have hP0 : 0 ≤ P := by linarith
  let T : ℝ := P^(max c 0)
  have hT : 1 ≤ T := Real.one_le_rpow hP1 (le_max_right _ _)
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hc : P^c ≤ T := Real.rpow_le_rpow_of_exponent_le hP1 (le_max_left _ _)
  have hv := hvol K F A W hAc hAd hAW T hT
    (fun J hJ => (hWnorm J hJ).trans hc)
    (fun J hJ v hV => (hWpiv J hJ v hV).trans
      (mul_le_mul_of_nonneg_right hc (by apply Real.sqrt_nonneg)))
  have heqPow : ENNReal.ofReal T^(24*M) = ENNReal.ofReal (P^b) := by
    rw [← ENNReal.ofReal_pow hT0]
    congr 1
    exact (Real.rpow_mul_natCast hP0 (max c 0) (24*M)).symm
  rw [heqPow] at hv
  calc
    _ ≤ (N:ℝ≥0∞)*ENNReal.ofReal (2*C^M)^4*ENNReal.ofReal (P^b) := hv
    _ ≤ ENNReal.ofReal A0*ENNReal.ofReal (P^b) := mul_le_mul_right' hAnn _
    _ = ENNReal.ofReal (A0*P^b) := (ENNReal.ofReal_mul (le_trans (by norm_num) hA0)).symm

end PaperI
