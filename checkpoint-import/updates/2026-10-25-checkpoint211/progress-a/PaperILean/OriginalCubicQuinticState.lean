import PaperILean.OriginalCubicQuinticRatio

/-! The actual quintic of x-syz+gz^3, with the original split degree cap.
The inherited complete Gram calculation supplies the attained least energy. -/
noncomputable section
open scoped BigOperators
open Filter Topology MvPolynomial
namespace PaperI

def originalCubicQuinticState (k : ℕ) (s g : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) : AugmentedState k :=
  (originalCenteredCubicProfile k s g ((Polynomial.X : Polynomial ℝ)^5)
    (by simpa using hk),0)

theorem originalCubicQuinticState_polynomial (k : ℕ) (s g : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) :
    coefficientPolynomial (originalCubicQuinticState k s g hk).1 =
      originalCenteredCubicInvariant s g^5 := by
  dsimp only [originalCubicQuinticState]
  rw [originalCenteredCubicProfile_polynomial]
  norm_num [Polynomial.eval₂_pow,Polynomial.eval₂_X]

theorem originalCubicQuinticState_profile (k : ℕ) (s g : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) :
    coefficientPolynomial (originalCubicQuinticState k s g hk).1 =
      ((Polynomial.X : Polynomial ℝ)^5).eval₂ C (originalCenteredCubicInvariant s g)-
        C (((Polynomial.X : Polynomial ℝ)^5).coeff 0) := by
  simpa using originalCubicQuinticState_polynomial k s g hk

theorem originalCubicQuinticState_rank (k : ℕ) {s : ℝ} (hs : s ≠ 0) (g : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) :
    (augmentedOrbitMatrix k (originalCubicQuinticState k s g hk)).rank = 4 := by
  have hk2 : 2 ≤ k := by split_ifs at hk <;> omega
  have hh := originalCenteredCubicFamily_rank hk2 (originalCubicQuinticState k s g hk).1
    hs g ((Polynomial.X : Polynomial ℝ)^5) (by simp)
    (originalCubicQuinticState_profile k s g hk) 0 0
  simpa [originalCenteredCubicFamily,originalCubicQuinticState] using hh

theorem originalCubicQuinticState_norm_sq (k : ℕ) (s g : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) :
    augmentedStateNorm (originalCubicQuinticState k s g hk)^2 = originalCubicQuinticNormSq s g := by
  change augmentedStateNorm ((originalCubicQuinticState k s g hk).1,0)^2 = _
  rw [original_zero_physical_norm_sq,original_coefficientEuclideanNorm_sq_support,
    originalCubicQuinticState_polynomial]
  change originalFullCoefficientNormSq (originalCenteredCubicInvariant s g^5) = _
  rw [original_centered_cubic_fifth_norm]
  unfold originalCubicQuinticNormSq
  ring

theorem originalCubicQuinticState_x_energy (k : ℕ) (s g : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) :
    coefficientEuclideanNorm (directionalCoefficientMap k (Pi.single 0 1)
      (originalCubicQuinticState k s g hk).1)^2 = 25*(1+16*g^2+36*g^4+16*g^6+g^8+16*s^2+144*s^2*g^2+144*s^2*g^4+16*s^2*g^6+36*s^4+144*s^4*g^2+36*s^4*g^4+16*s^6+16*s^6*g^2+s^8) := by
  rw [original_centered_cubic_x_energy_power_sum _ s g ((Polynomial.X : Polynomial ℝ)^5)
    (originalCubicQuinticState_profile k s g hk)]
  norm_num [original_centered_cubic_fourth_norm] <;> ring

theorem originalCubicQuinticState_translation_lower (k : ℕ) (s g : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) (h : PhysicalSpace) :
    originalCubicQuinticMinEnergy s g * physicalEuclideanNorm h^2 ≤
      augmentedStateNorm (augmentedOrbitDifferential k (originalCubicQuinticState k s g hk)
        (upperAffineTranslationCoordinates h))^2 := by
  have hh := original_centered_cubic_zero_linear_translation_lower
    (originalCubicQuinticState k s g hk).1 s g ((Polynomial.X : Polynomial ℝ)^5)
    (originalCubicQuinticState_profile k s g hk) (by simp) h
  rw [originalCubicQuinticState_x_energy] at hh
  exact hh

theorem originalCubicQuinticState_translation_attained (k : ℕ) (s g : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) :
    ∃ h : PhysicalSpace, physicalEuclideanNorm h = 1 ∧
      augmentedStateNorm (augmentedOrbitDifferential k (originalCubicQuinticState k s g hk)
        (upperAffineTranslationCoordinates h))^2 = originalCubicQuinticMinEnergy s g := by
  have hh := original_centered_cubic_zero_linear_translation_attained
    (originalCubicQuinticState k s g hk).1 s g ((Polynomial.X : Polynomial ℝ)^5)
    (originalCubicQuinticState_profile k s g hk) (by simp)
  simp only [originalCubicQuinticState_x_energy] at hh
  exact hh

theorem original_centered_quintic_expansion (s g : ℝ) :
    originalCenteredCubicInvariant s g^5 =
      X 0^5 +
      C (5*g)*(X 0^4*X 2^3) +
      C (10*g^2)*(X 0^3*X 2^6) +
      C (10*g^3)*(X 0^2*X 2^9) +
      C (5*g^4)*(X 0*X 2^12) +
      C (g^5)*(X 2^15) -
      C (5*s)*(X 0^4*X 1*X 2) -
      C (20*s*g)*(X 0^3*X 1*X 2^4) -
      C (30*s*g^2)*(X 0^2*X 1*X 2^7) -
      C (20*s*g^3)*(X 0*X 1*X 2^10) -
      C (5*s*g^4)*(X 1*X 2^13) +
      C (10*s^2)*(X 0^3*X 1^2*X 2^2) +
      C (30*s^2*g)*(X 0^2*X 1^2*X 2^5) +
      C (30*s^2*g^2)*(X 0*X 1^2*X 2^8) +
      C (10*s^2*g^3)*(X 1^2*X 2^11) -
      C (10*s^3)*(X 0^2*X 1^3*X 2^3) -
      C (20*s^3*g)*(X 0*X 1^3*X 2^6) -
      C (10*s^3*g^2)*(X 1^3*X 2^9) +
      C (5*s^4)*(X 0*X 1^4*X 2^4) +
      C (5*s^4*g)*(X 1^4*X 2^7) -
      C (s^5)*(X 1^5*X 2^5) := by
  simp only [originalCenteredCubicInvariant,map_mul,map_pow,map_ofNat]
  ring

theorem originalCubicQuinticState_continuous (k : ℕ) (s g : ℝ → ℝ)
    (hs : Continuous s) (hg : Continuous g)
    (hk : ∀ t, (if g t = 0 then 2 else 3)*5 ≤ k) :
    Continuous (fun t => originalCubicQuinticState k (s t) (g t) (hk t)) := by
  apply Continuous.prodMk ?_ continuous_const
  apply continuous_pi
  intro α
  have he : (fun t => (originalCubicQuinticState k (s t) (g t) (hk t)).1 α) =
      (fun t => coeff (monomialExponent α) (originalCenteredCubicInvariant (s t) (g t)^5)) := by
    funext t
    rw [← coefficientPolynomial_coeff (originalCubicQuinticState k (s t) (g t) (hk t)).1 α,
      originalCubicQuinticState_polynomial]
  change Continuous (fun t => (originalCubicQuinticState k (s t) (g t) (hk t)).1 α)
  rw [he]
  simp only [original_centered_quintic_expansion,coeff_add,coeff_sub,coeff_C_mul]
  fun_prop

theorem originalCubicQuintic_scaled_g_cap {k : ℕ} (g : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) (t : ℝ) :
    (if t*g = 0 then 2 else 3)*5 ≤ k := by
  by_cases hg : g = 0
  · simpa [hg] using hk
  · simp only [hg,if_false] at hk
    split_ifs <;> omega

end PaperI
