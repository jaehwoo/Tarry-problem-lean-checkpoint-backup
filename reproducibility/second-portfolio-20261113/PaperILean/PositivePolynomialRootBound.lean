import PaperILean.ParametricPolynomialBounds

/-! Uniform eventual lower bounds for every positive root. This algebraic
route neither selects a root branch nor assumes its continuity. -/

noncomputable section
open Filter Polynomial
namespace PaperI

theorem parametric_polynomial_positive_roots_lower_of_constant_ne_zero
    (q : Polynomial (Polynomial ℝ)) (hq : q.coeff 0 ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ᶠ P : ℝ in atTop, ∀ t : ℝ, 0 < t →
      q.eval₂ (Polynomial.evalRingHom P) t = 0 → c / P ^ N ≤ t := by
  rcases nonzero_polynomial_eventually_abs_lower (q.coeff 0) hq with ⟨b, hb, hlow⟩
  rcases parametric_polynomial_uniform_small_value_bound q.divX with ⟨B, hB, N, hupper⟩
  let c : ℝ := min 1 (b / B)
  have hc : 0 < c := lt_min zero_lt_one (div_pos hb hB)
  refine ⟨c, hc, N, ?_⟩
  filter_upwards [hlow, eventually_ge_atTop (1 : ℝ)] with P hlow hP
  intro t ht hr
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hpow : 0 < P ^ N := pow_pos hP0 _
  apply (div_le_iff₀ hpow).mpr
  by_cases ht1 : t ≤ 1
  · have hcB : c * B ≤ b := (le_div_iff₀ hB).mp (min_le_right _ _)
    have hb' : b ≤ (t * P ^ N) * B := calc
      b ≤ |(q.coeff 0).eval P| := hlow
      _ ≤ t * |q.divX.eval₂ (Polynomial.evalRingHom P) t| :=
        parametric_polynomial_constant_abs_le_root_mul_tail q ht.le hr
      _ ≤ t * (B * P ^ N) := mul_le_mul_of_nonneg_left
        (hupper P hP t (by rwa [abs_of_pos ht])) ht.le
      _ = (t * P ^ N) * B := by ring
    exact (mul_le_mul_right hB).mp (hcB.trans hb')
  · exact (min_le_left _ _).trans ((le_of_not_ge ht1).trans
      (le_mul_of_one_le_right ht.le (one_le_pow₀ hP)))

theorem parametric_polynomial_remove_zero_root
    (q : Polynomial (Polynomial ℝ)) (hq : q ≠ 0) :
    ∃ (r : Polynomial (Polynomial ℝ)) (n : ℕ),
      q = Polynomial.X ^ n * r ∧ r.coeff 0 ≠ 0 := by
  rcases Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq 0 with
    ⟨r, he, hr⟩
  simp only [map_zero, sub_zero] at he hr
  exact ⟨r, q.rootMultiplicity 0, he, fun hz => hr (Polynomial.X_dvd_iff.mpr hz)⟩

theorem parametric_polynomial_positive_roots_eventually_lower
    (q : Polynomial (Polynomial ℝ)) (hq : q ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ᶠ P : ℝ in atTop, ∀ t : ℝ, 0 < t →
      q.eval₂ (Polynomial.evalRingHom P) t = 0 → c / P ^ N ≤ t := by
  rcases parametric_polynomial_remove_zero_root q hq with ⟨r, n, he, hr⟩
  rcases parametric_polynomial_positive_roots_lower_of_constant_ne_zero r hr with
    ⟨c, hc, N, hbound⟩
  refine ⟨c, hc, N, ?_⟩
  filter_upwards [hbound] with P hbound
  intro t ht hroot
  apply hbound t ht
  rw [he, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ (ne_of_gt ht))

theorem parametric_polynomial_positive_roots_threshold_lower
    (q : Polynomial (Polynomial ℝ)) (hq : q ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∃ T : ℝ, 2 ≤ T ∧
      ∀ P : ℝ, T ≤ P → ∀ t : ℝ, 0 < t →
        q.eval₂ (Polynomial.evalRingHom P) t = 0 → c / P ^ N ≤ t := by
  rcases parametric_polynomial_positive_roots_eventually_lower q hq with ⟨c, hc, N, he⟩
  rcases Filter.eventually_atTop.mp he with ⟨T, hT⟩
  exact ⟨c, hc, N, max 2 T, le_max_left _ _, fun P hP =>
    hT P ((le_max_right _ _).trans hP)⟩

end PaperI
