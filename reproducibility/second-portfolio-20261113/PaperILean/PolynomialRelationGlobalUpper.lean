import PaperILean.PolynomialRootUpperBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! I625-638: bounded-window patching and the source's one-constant C*P^C
upper bound. No continuity or positivity of the function is required. -/

noncomputable section
namespace PaperI

theorem absorb_positive_coefficient_in_power (B : ℝ) (hB : 0 < B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → B * P ^ N ≤ C * P ^ C := by
  refine ⟨max B ((N : ℝ) + 1), lt_max_of_lt_left hB, ?_⟩
  intro P hP
  have hP1 : 1 ≤ P := le_trans (by norm_num) hP
  have hpow : P ^ N ≤ P ^ max B ((N : ℝ) + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hP1
      ((by linarith : (N : ℝ) ≤ (N : ℝ) + 1).trans (le_max_right _ _))
  exact mul_le_mul (le_max_left _ _) hpow (pow_nonneg (by linarith) _)
    (le_of_lt (lt_max_of_lt_left hB))

theorem bivariate_polynomial_real_roots_rpow_upper
    (q : MvPolynomial (Unit ⊕ Unit) ℝ) (hq : q ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 2 ≤ T ∧
      ∀ P : ℝ, T ≤ P → ∀ t : ℝ,
        MvPolynomial.eval (polynomialGraphCoordinates (fun _ => P) t) q = 0 →
          |t| ≤ C * P ^ C := by
  obtain ⟨B, hB, N, T, hT, hbound⟩ :=
    bivariate_polynomial_real_roots_threshold_upper q hq
  obtain ⟨C, hC, hCbound⟩ := absorb_positive_coefficient_in_power B hB N
  exact ⟨C, hC, T, hT, fun P hP t hr =>
    (hbound P hP t hr).trans (hCbound P (hT.trans hP))⟩

theorem function_polynomial_relation_global_upper
    (m : ℝ → ℝ)
    (hwindow : ∀ T : ℝ, ∃ b : ℝ, 0 < b ∧
      ∀ P : ℝ, 2 ≤ P → P ≤ T → |m P| ≤ b)
    (q : MvPolynomial (Unit ⊕ Unit) ℝ) (hq : q ≠ 0)
    (hrel : ∀ P : ℝ, 2 ≤ P →
      MvPolynomial.eval (polynomialGraphCoordinates (fun _ => P) (m P)) q = 0) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∀ P : ℝ, 2 ≤ P → |m P| ≤ B * P ^ N := by
  obtain ⟨B, hB, N, T, hT, hbound⟩ :=
    bivariate_polynomial_real_roots_threshold_upper q hq
  obtain ⟨b, hb, hwindow⟩ := hwindow T
  refine ⟨max B b, lt_max_of_lt_left hB, N, ?_⟩
  intro P hP
  have hP1 : 1 ≤ P := le_trans (by norm_num) hP
  by_cases hPT : P ≤ T
  · exact (hwindow P hP hPT).trans ((le_max_right _ _).trans
      (le_mul_of_one_le_right (le_of_lt (lt_max_of_lt_left hB)) (one_le_pow₀ hP1)))
  · exact (hbound P (le_of_not_ge hPT) (m P) (hrel P hP)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _))

theorem function_polynomial_relation_rpow_upper
    (m : ℝ → ℝ)
    (hwindow : ∀ T : ℝ, ∃ b : ℝ, 0 < b ∧
      ∀ P : ℝ, 2 ≤ P → P ≤ T → |m P| ≤ b)
    (q : MvPolynomial (Unit ⊕ Unit) ℝ) (hq : q ≠ 0)
    (hrel : ∀ P : ℝ, 2 ≤ P →
      MvPolynomial.eval (polynomialGraphCoordinates (fun _ => P) (m P)) q = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → |m P| ≤ C * P ^ C := by
  obtain ⟨B, hB, N, hbound⟩ :=
    function_polynomial_relation_global_upper m hwindow q hq hrel
  obtain ⟨C, hC, hCbound⟩ := absorb_positive_coefficient_in_power B hB N
  exact ⟨C, hC, fun P hP => (hbound P hP).trans (hCbound P hP)⟩

end PaperI

