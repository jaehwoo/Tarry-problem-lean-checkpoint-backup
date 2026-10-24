import PaperILean.OriginalCubicQuinticState

/-! Original I773 compact-minimum application: exclude the entire centered
pure-quintic branch, preserving the quadratic/cubic degree split and same A. -/
noncomputable section
open Filter Topology MvPolynomial
namespace PaperI

theorem original_scaledCubicQuintic_norm_sq (k : ℕ) (s g c : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) :
    augmentedStateNorm (c • originalCubicQuinticState k s g hk)^2 =
      c^2*originalCubicQuinticNormSq s g := by
  rw [augmentedStateNorm_smul,mul_pow,sq_abs,originalCubicQuinticState_norm_sq]

theorem original_scaledCubicQuintic_norm_pos (k : ℕ) (s g c : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) (hc : c ≠ 0) :
    0 < augmentedStateNorm (c • originalCubicQuinticState k s g hk) := by
  have hp := mul_pos (sq_pos_of_ne_zero hc) (originalCubicQuintic_norm_pos s g)
  rw [← original_scaledCubicQuintic_norm_sq k s g c hk] at hp
  nlinarith [augmentedStateNorm_nonneg (c • originalCubicQuinticState k s g hk)]

theorem original_scaledCubicQuintic_translation_lower (k : ℕ) (s g c : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) (h : PhysicalSpace) :
    (c^2*originalCubicQuinticMinEnergy s g)*physicalEuclideanNorm h^2 ≤
      augmentedStateNorm (augmentedOrbitDifferential k (c • originalCubicQuinticState k s g hk)
        (upperAffineTranslationCoordinates h))^2 := by
  rw [original_augmentedOrbit_state_smul,augmentedStateNorm_smul,mul_pow,sq_abs]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (originalCubicQuinticState_translation_lower k s g hk h) (sq_nonneg c)

theorem original_scaledCubicQuintic_translation_attained (k : ℕ) (s g c : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) :
    ∃ h : PhysicalSpace, physicalEuclideanNorm h = 1 ∧
      augmentedStateNorm (augmentedOrbitDifferential k (c • originalCubicQuinticState k s g hk)
        (upperAffineTranslationCoordinates h))^2 = c^2*originalCubicQuinticMinEnergy s g := by
  obtain ⟨h,hh,he⟩ := originalCubicQuinticState_translation_attained k s g hk
  refine ⟨h,hh,?_⟩
  rw [original_augmentedOrbit_state_smul,augmentedStateNorm_smul,mul_pow,sq_abs,he]

theorem original_scaledCubicQuintic_far_closure_ratio {k N : ℕ} {A B : ℝ}
    {s : ℝ} (hs : s ≠ 0) (g c : ℝ) (hc : c ≠ 0)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) (hA : 2 ≤ A)
    (ht : AugmentedTranslationStopped A (c • originalCubicQuinticState k s g hk))
    (hcl : (A,c • originalCubicQuinticState k s g hk) ∈ closure (originalFarBoundedFamily k N B)) :
    augmentedStateNorm (c • originalCubicQuinticState k s g hk) = A ∧
      originalCubicQuinticNormSq s g = A^4*originalCubicQuinticMinEnergy s g := by
  have hr := (original_augmentedOrbit_rank_smul c hc _).trans
    (originalCubicQuinticState_rank k hs g hk)
  have hn : augmentedStateNorm (c • originalCubicQuinticState k s g hk) = A := by
    apply le_antisymm ht.1
    by_contra! hlt
    exact original_norm_slack_not_mem_far_closure hA _ ht hr hlt hcl
  have he : c^2*originalCubicQuinticMinEnergy s g = A ^ (-2 : ℤ) := by
    apply le_antisymm
    · by_contra! hlt
      exact original_translation_slack_not_mem_far_closure hA _ ht hr hlt
        (original_scaledCubicQuintic_translation_lower k s g c hk) hcl
    · obtain ⟨h,hh,he⟩ := original_scaledCubicQuintic_translation_attained k s g c hk
      have ht' := ((augmentedTranslationStopped_iff_orbit A _).mp ht).2 h
      simpa only [hh,one_pow,mul_one,he] using ht'
  have hn2 : c^2*originalCubicQuinticNormSq s g = A^2 := by
    rw [← original_scaledCubicQuintic_norm_sq,hn]
  refine ⟨hn,?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hc)
  calc
    c^2*originalCubicQuinticNormSq s g = A^2 := hn2
    _ = A^4*A ^ (-2 : ℤ) := by
      have hA0 : A ≠ 0 := by linarith
      norm_num only [zpow_neg,zpow_ofNat]
      field_simp
      ring
    _ = A^4*(c^2*originalCubicQuinticMinEnergy s g) := by rw [he]
    _ = c^2*(A^4*originalCubicQuinticMinEnergy s g) := by ring

theorem original_scaledCubicQuintic_not_mem_far_closure {k N : ℕ} {A B : ℝ}
    {s : ℝ} (hs : s ≠ 0) (g c : ℝ) (hc : c ≠ 0)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k) (hA : 2 ≤ A)
    (ht : AugmentedTranslationStopped A (c • originalCubicQuinticState k s g hk)) :
    (A,c • originalCubicQuinticState k s g hk) ∉ closure (originalFarBoundedFamily k N B) := by
  intro hcl
  obtain ⟨hn,he⟩ := original_scaledCubicQuintic_far_closure_ratio hs g c hc hk hA ht hcl
  by_cases hg : g = 0
  · subst g
    have hf := originalHyperbolicQuintic_min_ratio_improvement hA hs
      (by simpa only [(originalCubicQuintic_zero_data s).1,
        (originalCubicQuintic_zero_data s).2] using he)
    have hcont : Continuous (fun b : ℝ => c • originalCubicQuinticState k b 0 hk) := continuous_const.smul
      (originalCubicQuinticState_continuous k id (fun _ => 0) continuous_id continuous_const (fun _ => hk))
    refine original_curve_strict_ratio_not_mem_far_closure hA
      (fun b => c • originalCubicQuinticState k b 0 hk) hcont.continuousAt hn ?_ hcl
    apply hf.mono
    rintro b ⟨hb,hbetter⟩
    refine ⟨original_scaledCubicQuintic_norm_pos k b 0 c hk hc,
      (original_augmentedOrbit_rank_smul c hc _).trans (originalCubicQuinticState_rank k hb 0 hk),
      c^2*originalCubicQuinticMinEnergy b 0,
      original_scaledCubicQuintic_translation_lower k b 0 c hk,?_⟩
    rw [original_scaledCubicQuintic_norm_sq]
    have hh : originalCubicQuinticNormSq b 0 < A^4*originalCubicQuinticMinEnergy b 0 := by
      simpa only [(originalCubicQuintic_zero_data b).1,(originalCubicQuintic_zero_data b).2] using hbetter
    nlinarith [mul_lt_mul_of_pos_left hh (sq_pos_of_ne_zero hc)]
  · let cap := originalCubicQuintic_scaled_g_cap g hk
    let U := fun b => c • originalCubicQuinticState k s (b*g) (cap b)
    have hU : U 1 = c • originalCubicQuinticState k s g hk := by simp [U]
    have hcont : Continuous U := continuous_const.smul
      (originalCubicQuinticState_continuous k (fun _ => s) (fun b => b*g)
        continuous_const (continuous_id.mul continuous_const) cap)
    have hexcl : (A,U 1) ∉ closure (originalFarBoundedFamily k N B) := by
      apply original_curve_strict_ratio_not_mem_far_closure hA U hcont.continuousAt (by rwa [hU])
      apply (originalCubicQuintic_g_ratio_improvement hs hg he).mono
      rintro b ⟨hb,hb1,hbetter⟩
      refine ⟨original_scaledCubicQuintic_norm_pos k s (b*g) c (cap b) hc,
        (original_augmentedOrbit_rank_smul c hc _).trans (originalCubicQuinticState_rank k hs (b*g) (cap b)),
        c^2*originalCubicQuinticMinEnergy s (b*g),
        original_scaledCubicQuintic_translation_lower k s (b*g) c (cap b),?_⟩
      change augmentedStateNorm (c • originalCubicQuinticState k s (b*g) (cap b))^2 < _
      rw [original_scaledCubicQuintic_norm_sq]
      nlinarith [mul_lt_mul_of_pos_left hbetter (sq_pos_of_ne_zero hc)]
    exact hexcl (by simpa only [hU] using hcl)

theorem original_centered_quintic_state_eq {k : ℕ} (F : CoefficientSpace k) (s g c : ℝ)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k)
    (hF : coefficientPolynomial F = C c*originalCenteredCubicInvariant s g^5) :
    (F,0) = c • originalCubicQuinticState k s g hk := by
  apply Prod.ext
  · change F = c • (originalCubicQuinticState k s g hk).1
    apply (coefficientPolynomialEquiv k).injective
    apply Subtype.ext
    change coefficientPolynomial F = ((coefficientPolynomialEquiv k) (c • _)).val
    rw [map_smul]
    change coefficientPolynomial F = c • coefficientPolynomial (originalCubicQuinticState k s g hk).1
    rw [hF,originalCubicQuinticState_polynomial,smul_eq_C_mul]
  · simp [originalCubicQuinticState]

theorem original_centered_quintic_not_mem_far_closure {k N : ℕ}
    (F : CoefficientSpace k) {s : ℝ} (hs : s ≠ 0) (g c : ℝ) (hc : c ≠ 0)
    (hk : (if g = 0 then 2 else 3)*5 ≤ k)
    (hF : coefficientPolynomial F = C c*originalCenteredCubicInvariant s g^5)
    {A B : ℝ} (hA : 2 ≤ A) (ht : AugmentedTranslationStopped A (F,0)) :
    (A,(F,0)) ∉ closure (originalFarBoundedFamily k N B) := by
  have he := original_centered_quintic_state_eq F s g c hk hF
  rw [he] at ht ⊢
  exact original_scaledCubicQuintic_not_mem_far_closure hs g c hc hk hA ht

theorem original_centered_far_closure_quintic_zero {k N : ℕ}
    (F : CoefficientSpace k) {s : ℝ} (hs : s ≠ 0) (g : ℝ) (f : Polynomial ℝ)
    (hf : 2 ≤ f.natDegree) (hcap : (if g = 0 then 2 else 3)*f.natDegree ≤ k)
    (hF : coefficientPolynomial F = f.eval₂ C (originalCenteredCubicInvariant s g)-C (f.coeff 0))
    {A B : ℝ} (hA : 2 ≤ A) (ht : AugmentedTranslationStopped A (F,0))
    (hcl : (A,(F,0)) ∈ closure (originalFarBoundedFamily k N B)) : f.coeff 5 = 0 := by
  by_contra ha
  have hphase := original_centered_far_closure_fifth_phase F hs g f hf hcap hF hA ht hcl ha
  have hd : 5 ≤ f.natDegree := Polynomial.le_natDegree_of_ne_zero ha
  have hk : (if g = 0 then 2 else 3)*5 ≤ k := (Nat.mul_le_mul_left _ hd).trans hcap
  exact original_centered_quintic_not_mem_far_closure F hs g (f.coeff 5) ha hk hphase hA ht hcl

theorem original_centered_far_closure_through_quintic_zero {k N : ℕ}
    (F : CoefficientSpace k) {s : ℝ} (hs : s ≠ 0) (g : ℝ) (f : Polynomial ℝ)
    (hf : 2 ≤ f.natDegree) (hcap : (if g = 0 then 2 else 3)*f.natDegree ≤ k)
    (hF : coefficientPolynomial F = f.eval₂ C (originalCenteredCubicInvariant s g)-C (f.coeff 0))
    {A B : ℝ} (hA : 2 ≤ A) (ht : AugmentedTranslationStopped A (F,0))
    (hcl : (A,(F,0)) ∈ closure (originalFarBoundedFamily k N B)) :
    f.coeff 1 = 0 ∧ f.coeff 2 = 0 ∧ f.coeff 3 = 0 ∧ f.coeff 4 = 0 ∧ f.coeff 5 = 0 ∧ 6 ≤ f.natDegree := by
  obtain ⟨ha1,ha2,ha3,ha4,hf5⟩ := original_centered_far_closure_through_quartic_zero F hs g f hf hcap hF hA ht hcl
  have ha5 := original_centered_far_closure_quintic_zero F hs g f hf hcap hF hA ht hcl
  refine ⟨ha1,ha2,ha3,ha4,ha5,?_⟩
  by_contra! hd
  have hd4 : f.natDegree ≤ 4 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases hn5 : n = 5
    · simpa only [hn5] using ha5
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  omega

end PaperI
