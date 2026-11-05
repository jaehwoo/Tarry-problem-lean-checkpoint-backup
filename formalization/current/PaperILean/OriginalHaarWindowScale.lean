import PaperILean.OriginalHaarWindowVolume

/-! Elementary scale growth for the actual Haar bound. Constants depend only
on the fixed coefficient dimension and fixed-format piece/component bounds. -/
noncomputable section
namespace PaperI
open scoped ENNReal

/-- The relative-coordinate bound grows by at most the sixth power in the
common coefficient/inverse-pivot bound A>=1. -/
theorem originalHaar_relative_scale_bound (n : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    let L : ℝ := A*(n:ℝ)*(2*A)
    let C : ℝ := 1+4*(n:ℝ)*(1+2*(n:ℝ))^2
    1+2*(L*(1+L)^2) ≤ C*A^6 := by
  dsimp only
  let L : ℝ := A*(n:ℝ)*(2*A)
  let c : ℝ := 2*(n:ℝ)
  have hAn : 0 ≤ A := le_trans (by norm_num) hA
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLe : L=c*A^2 := by dsimp [L,c]; ring
  have hA2 : 1 ≤ A^2 := one_le_pow₀ hA
  have hA6 : 1 ≤ A^6 := one_le_pow₀ hA
  have h1 : 1+L ≤ (1+c)*A^2 := by rw [hLe]; nlinarith
  have hq : L*(1+L)^2 ≤ (c*(1+c)^2)*A^6 := by
    calc
      _ ≤ L*((1+c)*A^2)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ 1+L) h1 2) hL
      _ = (c*(1+c)^2)*A^6 := by rw [hLe]; ring
  change 1+2*(L*(1+L)^2) ≤ _
  have he : 1+4*(n:ℝ)*(1+2*(n:ℝ))^2 = 1+2*c*(1+c)^2 := by dsimp [c]; ring
  rw [he]
  nlinarith

/-- The finite piece exponent remains fixed before every phase and scale. -/
theorem originalHaar_relative_power_scale_bound (n M : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    let L : ℝ := A*(n:ℝ)*(2*A)
    let C : ℝ := 1+4*(n:ℝ)*(1+2*(n:ℝ))^2
    (1+2*(L*(1+L)^2))^M ≤ C^M*A^(6*M) := by
  dsimp only
  have h := originalHaar_relative_scale_bound n A hA
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hL0 : 0 ≤ A*(n:ℝ)*(2*A) := by positivity
  calc
    _ ≤ ((1+4*(n:ℝ)*(1+2*(n:ℝ))^2)*A^6)^M :=
      pow_le_pow_left₀ (by positivity) h M
    _ = (1+4*(n:ℝ)*(1+2*(n:ℝ))^2)^M*A^(6*M) := by
      rw [mul_pow,← pow_mul]

/-- One explicit polynomial growth bound for every actual subgroup orbit.
The displayed constants precede the scale and every phase/window instance. -/
theorem originalHaarOrbitWindow_scaled_volume_stage
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) :
    ∃ N M : ℕ, ∀ (K : OriginalHaarSubgroup) (F : CoefficientSpace k)
      (A : Finset (MvPolynomial (MonomialIndex k) ℝ)) (W : Set (CoefficientSpace k)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A W →
      ∀ T : ℝ, 1 ≤ T →
      (∀ J ∈ W, coefficientEuclideanNorm J ≤ T) →
      (∀ J ∈ W, ∀ v ∈ originalHaarSubgroupSet K,
        coordinateL2Norm v ≤ T*coefficientEuclideanNorm (originalHaarPhysicalLieAction J v)) →
      let C : ℝ := 1+4*(Fintype.card (MonomialIndex k):ℝ)*
        (1+2*(Fintype.card (MonomialIndex k):ℝ))^2
      OriginalHaarWindowMeasures.subgroupHaar K (originalHaarOrbitWindow K F W) ≤
        (N:ℝ≥0∞)*ENNReal.ofReal (2*C^M)^4*ENNReal.ofReal T^(24*M) := by
  obtain ⟨N,M,hvol⟩ := originalHaarOrbitWindow_volume_stage hCell hPath hHardt hQE hNash hPiece k s D
  refine ⟨N,M,?_⟩
  intro K F A W hAc hAd hAW T hT hWnorm hWpiv
  dsimp only
  let n := Fintype.card (MonomialIndex k)
  let C : ℝ := 1+4*(n:ℝ)*(1+2*(n:ℝ))^2
  let L : ℝ := T*(n:ℝ)*(2*T)
  let R : ℝ := L*(1+L)^2
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hbound := originalHaar_relative_power_scale_bound n M T hT
  have h := hvol K F A W hAc hAd hAW T T hT0 hT0 hWnorm hWpiv
  calc
    _ ≤ (N:ℝ≥0∞)*ENNReal.ofReal (2*((1+2*R)^M))^4 := h
    _ ≤ (N:ℝ≥0∞)*ENNReal.ofReal (2*(C^M*T^(6*M)))^4 := by
      gcongr
    _ = (N:ℝ≥0∞)*ENNReal.ofReal (2*C^M)^4*ENNReal.ofReal T^(24*M) := by
      rw [show 2*(C^M*T^(6*M))=(2*C^M)*T^(6*M) by ring,
        ENNReal.ofReal_mul (by positivity : 0 ≤ 2*C^M),
        ENNReal.ofReal_pow hT0 (6*M),mul_pow,← pow_mul]
      rw [show 6*M*4=24*M by omega,mul_assoc]

end PaperI
