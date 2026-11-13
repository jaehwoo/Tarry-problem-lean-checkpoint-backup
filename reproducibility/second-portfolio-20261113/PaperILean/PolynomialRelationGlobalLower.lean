import PaperILean.BivariatePolynomialRootBound

/-! Extend the eventual estimate using the separately proved bounded-window
bounds. Neither global continuity nor continuity of a minimum is used. -/

noncomputable section
namespace PaperI

theorem positive_function_polynomial_relation_global_lower
    (m : ℝ → ℝ) (hpos : ∀ P : ℝ, 2 ≤ P → 0 < m P)
    (hwindow : ∀ T : ℝ, ∃ b : ℝ, 0 < b ∧
      ∀ P : ℝ, 2 ≤ P → P ≤ T → b ≤ m P)
    (q : MvPolynomial (Unit ⊕ Unit) ℝ) (hq : q ≠ 0)
    (hrel : ∀ P : ℝ, 2 ≤ P →
      MvPolynomial.eval (polynomialGraphCoordinates (fun _ => P) (m P)) q = 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ P : ℝ, 2 ≤ P → c / P ^ N ≤ m P := by
  rcases bivariate_polynomial_positive_roots_threshold_lower q hq with
    ⟨c, hc, N, T, hT, hbound⟩
  rcases hwindow T with ⟨b, hb, hwindow⟩
  refine ⟨min c b, lt_min hc hb, N, ?_⟩
  intro P hP
  have hP1 : 1 ≤ P := le_trans (by norm_num) hP
  have hpow : 0 < P ^ N := pow_pos (lt_of_lt_of_le (by norm_num) hP) _
  by_cases hPT : P ≤ T
  · exact (div_le_self (le_of_lt (lt_min hc hb)) (one_le_pow₀ hP1)).trans
      ((min_le_right _ _).trans (hwindow P hP hPT))
  · exact (div_le_div_of_nonneg_right (min_le_left _ _) hpow.le).trans
      (hbound P (le_of_not_ge hPT) (m P) (hpos P hP) (hrel P hP))

theorem absorb_positive_constant_in_inverse_power (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ P : ℝ, 2 ≤ P → 1 / P ^ M ≤ c / P ^ N := by
  rcases exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1) with ⟨n, hn⟩
  refine ⟨N + n + 1, by omega, ?_⟩
  intro P hP
  have hP1 : 1 ≤ P := le_trans (by norm_num) hP
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hsmall : 1 / P ^ n ≤ c := calc
    1 / P ^ n ≤ 1 / (2 : ℝ) ^ n :=
      one_div_le_one_div_of_le (pow_pos (by norm_num) _)
        (pow_le_pow_left₀ (by norm_num) hP _)
    _ ≤ c := by simpa only [div_pow, one_pow] using hn.le
  calc
    1 / P ^ (N + n + 1) ≤ 1 / P ^ (N + n) :=
      one_div_le_one_div_of_le (pow_pos hP0 _)
        (pow_le_pow_right₀ hP1 (by omega))
    _ = (1 / P ^ n) / P ^ N := by rw [div_div, pow_add, mul_comm]
    _ ≤ c / P ^ N := div_le_div_of_nonneg_right hsmall (pow_nonneg hP0.le _)

theorem bivariate_polynomial_positive_roots_rpow_lower
    (q : MvPolynomial (Unit ⊕ Unit) ℝ) (hq : q ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 2 ≤ T ∧
      ∀ P : ℝ, T ≤ P → ∀ t : ℝ, 0 < t →
        MvPolynomial.eval (polynomialGraphCoordinates (fun _ => P) t) q = 0 →
          P ^ (-C) ≤ t := by
  rcases bivariate_polynomial_positive_roots_threshold_lower q hq with
    ⟨c, hc, N, T, hT, hbound⟩
  rcases absorb_positive_constant_in_inverse_power c hc N with ⟨M, hM, hMbound⟩
  refine ⟨M, by exact_mod_cast hM, T, hT, ?_⟩
  intro P hP t ht hr
  have hP2 : 2 ≤ P := hT.trans hP
  have hP0 : 0 ≤ P := le_trans (by norm_num) hP2
  simpa only [Real.rpow_neg hP0, Real.rpow_natCast, one_div] using
    (hMbound P hP2).trans (hbound P hP t ht hr)

theorem positive_function_polynomial_relation_rpow_lower
    (m : ℝ → ℝ) (hpos : ∀ P : ℝ, 2 ≤ P → 0 < m P)
    (hwindow : ∀ T : ℝ, ∃ b : ℝ, 0 < b ∧
      ∀ P : ℝ, 2 ≤ P → P ≤ T → b ≤ m P)
    (q : MvPolynomial (Unit ⊕ Unit) ℝ) (hq : q ≠ 0)
    (hrel : ∀ P : ℝ, 2 ≤ P →
      MvPolynomial.eval (polynomialGraphCoordinates (fun _ => P) (m P)) q = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → P ^ (-C) ≤ m P := by
  rcases positive_function_polynomial_relation_global_lower m hpos hwindow q hq hrel with
    ⟨c, hc, N, hbound⟩
  rcases absorb_positive_constant_in_inverse_power c hc N with ⟨M, hM, hMbound⟩
  refine ⟨M, by exact_mod_cast hM, ?_⟩
  intro P hP
  have hP0 : 0 ≤ P := le_trans (by norm_num) hP
  simpa only [Real.rpow_neg hP0, Real.rpow_natCast, one_div] using
    (hMbound P hP).trans (hbound P hP)

end PaperI
