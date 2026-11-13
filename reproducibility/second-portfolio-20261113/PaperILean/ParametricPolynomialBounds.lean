import PaperILean.RealPolynomialGrowthBounds

/-! Polynomial in the value variable, with polynomial coefficients in the
parameter. Constants are chosen before both the parameter and the value. -/

noncomputable section
open Filter Polynomial
namespace PaperI

theorem parametric_polynomial_uniform_small_value_bound
    (q : Polynomial (Polynomial ℝ)) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∀ P : ℝ, 1 ≤ P → ∀ t : ℝ, |t| ≤ 1 →
      |q.eval₂ (Polynomial.evalRingHom P) t| ≤ B * P ^ N := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
      rcases hq with ⟨B, hB, N, hq⟩
      rcases hr with ⟨D, hD, M, hr⟩
      refine ⟨B + D, add_pos hB hD, N + M, ?_⟩
      intro P hP t ht
      rw [Polynomial.eval₂_add]
      calc
        |q.eval₂ (Polynomial.evalRingHom P) t + r.eval₂ (Polynomial.evalRingHom P) t|
            ≤ |q.eval₂ (Polynomial.evalRingHom P) t| +
              |r.eval₂ (Polynomial.evalRingHom P) t| := abs_add _ _
        _ ≤ B * P ^ N + D * P ^ M := add_le_add (hq P hP t ht) (hr P hP t ht)
        _ ≤ B * P ^ (N + M) + D * P ^ (N + M) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP (Nat.le_add_right N M)) hB.le)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP (Nat.le_add_left M N)) hD.le)
        _ = (B + D) * P ^ (N + M) := (add_mul _ _ _).symm
  | monomial n a =>
      rcases polynomial_exists_positive_power_upper_bound a with ⟨B, hB, N, ha⟩
      refine ⟨B, hB, N, ?_⟩
      intro P hP t ht
      simp only [Polynomial.eval₂_monomial, abs_mul, abs_pow]
      change |a.eval P| * |t| ^ n ≤ B * P ^ N
      exact (mul_le_of_le_one_right (abs_nonneg _)
        (pow_le_one₀ (abs_nonneg _) ht)).trans (ha P hP)

theorem parametric_polynomial_constant_abs_le_root_mul_tail
    (q : Polynomial (Polynomial ℝ)) {P t : ℝ} (ht : 0 ≤ t)
    (hr : q.eval₂ (Polynomial.evalRingHom P) t = 0) :
    |(q.coeff 0).eval P| ≤ t * |q.divX.eval₂ (Polynomial.evalRingHom P) t| := by
  have he := congrArg (fun r : Polynomial (Polynomial ℝ) =>
    r.eval₂ (Polynomial.evalRingHom P) t) (Polynomial.X_mul_divX_add q)
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
    Polynomial.eval₂_C, hr] at he
  change t * q.divX.eval₂ (Polynomial.evalRingHom P) t + (q.coeff 0).eval P = 0 at he
  have hc : (q.coeff 0).eval P = -(t * q.divX.eval₂ (Polynomial.evalRingHom P) t) := by
    linarith
  rw [hc, abs_neg, abs_mul, abs_of_nonneg ht]

end PaperI
