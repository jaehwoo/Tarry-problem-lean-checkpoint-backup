import PaperILean.BivariatePolynomialRootBound
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! I638: upper bounds for every real root of a fixed nonzero bivariate
polynomial. This uses the already proved positive-root lower bound, with
reversal and sign change. No branch is chosen and no continuity is assumed. -/

noncomputable section
namespace PaperI

theorem parametric_polynomial_inverse_root
    (q : Polynomial (Polynomial ℝ)) {P t : ℝ} (ht : t ≠ 0)
    (hr : q.eval₂ (Polynomial.evalRingHom P) t = 0) :
    q.reverse.eval₂ (Polynomial.evalRingHom P) t⁻¹ = 0 := by
  letI : Invertible t := invertibleOfNonzero ht
  simpa only [invOf_eq_inv] using
    (Polynomial.eval₂_reverse_eq_zero_iff (Polynomial.evalRingHom P) t q).mpr hr

theorem parametric_polynomial_positive_roots_threshold_upper
    (q : Polynomial (Polynomial ℝ)) (hq : q ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∃ T : ℝ, 2 ≤ T ∧
      ∀ P : ℝ, T ≤ P → ∀ t : ℝ, 0 < t →
        q.eval₂ (Polynomial.evalRingHom P) t = 0 → t ≤ B * P ^ N := by
  obtain ⟨c, hc, N, T, hT, hbound⟩ :=
    parametric_polynomial_positive_roots_threshold_lower q.reverse
      (fun h => hq (Polynomial.reverse_eq_zero.mp h))
  refine ⟨1 / c, div_pos zero_lt_one hc, N, T, hT, ?_⟩
  intro P hP t ht hr
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) (hT.trans hP)
  have h := hbound P hP t⁻¹ (inv_pos.mpr ht)
    (parametric_polynomial_inverse_root q ht.ne' hr)
  have hprod : c * t ≤ P ^ N := by
    have h' : c / P ^ N ≤ 1 / t := by simpa only [one_div] using h
    simpa only [one_mul] using (div_le_div_iff₀ (pow_pos hP0 N) ht).mp h'
  calc
    t ≤ P ^ N / c := (le_div_iff₀ hc).mpr (by nlinarith)
    _ = (1 / c) * P ^ N := by ring

theorem parametric_polynomial_neg_variable_ne_zero
    (q : Polynomial (Polynomial ℝ)) (hq : q ≠ 0) :
    q.comp (-Polynomial.X) ≠ 0 := by
  intro he
  have h : (q.comp (-Polynomial.X)).comp (-Polynomial.X) = 0 := by
    rw [he, Polynomial.zero_comp]
  exact hq (by simpa only [Polynomial.comp_neg_X_comp_neg_X] using h)

theorem parametric_polynomial_real_roots_threshold_upper
    (q : Polynomial (Polynomial ℝ)) (hq : q ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∃ T : ℝ, 2 ≤ T ∧
      ∀ P : ℝ, T ≤ P → ∀ t : ℝ,
        q.eval₂ (Polynomial.evalRingHom P) t = 0 → |t| ≤ B * P ^ N := by
  obtain ⟨Bpos, hBpos, Npos, Tpos, hTpos, hpos⟩ :=
    parametric_polynomial_positive_roots_threshold_upper q hq
  obtain ⟨Bneg, hBneg, Nneg, Tneg, hTneg, hneg⟩ :=
    parametric_polynomial_positive_roots_threshold_upper (q.comp (-Polynomial.X))
      (parametric_polynomial_neg_variable_ne_zero q hq)
  refine ⟨max Bpos Bneg, lt_max_of_lt_left hBpos, Npos + Nneg,
    max Tpos Tneg, hTpos.trans (le_max_left _ _), ?_⟩
  intro P hP t hr
  have hPpos : Tpos ≤ P := (le_max_left _ _).trans hP
  have hPneg : Tneg ≤ P := (le_max_right _ _).trans hP
  have hP1 : 1 ≤ P := le_trans (by norm_num) (hTpos.trans hPpos)
  have hbpos : Bpos * P ^ Npos ≤ max Bpos Bneg * P ^ (Npos + Nneg) :=
    mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hP1 (by omega))
      (pow_nonneg (by linarith) _) (le_of_lt (lt_max_of_lt_left hBpos))
  have hbneg : Bneg * P ^ Nneg ≤ max Bpos Bneg * P ^ (Npos + Nneg) :=
    mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hP1 (by omega))
      (pow_nonneg (by linarith) _) (le_of_lt (lt_max_of_lt_left hBpos))
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [abs_of_neg ht]
    apply (hneg P hPneg (-t) (neg_pos.mpr ht) ?_).trans hbneg
    simpa only [Polynomial.eval₂_comp, Polynomial.eval₂_neg,
      Polynomial.eval₂_X, neg_neg] using hr
  · subst t
    simpa only [abs_zero] using mul_nonneg
      (le_of_lt (lt_max_of_lt_left hBpos)) (pow_nonneg (by linarith) (Npos + Nneg))
  · rw [abs_of_pos ht]
    exact (hpos P hPpos t ht hr).trans hbpos

theorem bivariate_polynomial_real_roots_threshold_upper
    (q : MvPolynomial (Unit ⊕ Unit) ℝ) (hq : q ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∃ T : ℝ, 2 ≤ T ∧
      ∀ P : ℝ, T ≤ P → ∀ t : ℝ,
        MvPolynomial.eval (polynomialGraphCoordinates (fun _ => P) t) q = 0 →
          |t| ≤ B * P ^ N := by
  have hq' : bivariateToParametric q ≠ 0 := by
    intro h
    exact hq (bivariateToParametric_injective (by simpa only [map_zero] using h))
  obtain ⟨B, hB, N, T, hT, hb⟩ :=
    parametric_polynomial_real_roots_threshold_upper (bivariateToParametric q) hq'
  refine ⟨B, hB, N, T, hT, fun P hP t hr => hb P hP t ?_⟩
  simpa only [bivariateToParametric_eval] using hr

end PaperI

