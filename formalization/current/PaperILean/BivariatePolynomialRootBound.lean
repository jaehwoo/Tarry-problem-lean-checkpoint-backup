import PaperILean.PositivePolynomialRootBound
import PaperILean.SignGraphPolynomialRelation

/-! The first coordinate is the parameter P and the second the value t.
The change to nested polynomials is injective and preserves evaluation. -/

noncomputable section
open Polynomial
namespace PaperI

def bivariateToParametric :
    MvPolynomial (Unit ⊕ Unit) ℝ →+* Polynomial (Polynomial ℝ) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    (Sum.elim (fun _ => Polynomial.C Polynomial.X) (fun _ => Polynomial.X))

def parametricToBivariate :
    Polynomial (Polynomial ℝ) →+* MvPolynomial (Unit ⊕ Unit) ℝ :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (Sum.inl ())))
    (MvPolynomial.X (Sum.inr ()))

theorem parametricToBivariate_comp_bivariateToParametric :
    parametricToBivariate.comp bivariateToParametric = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [bivariateToParametric, parametricToBivariate]
  · intro i
    rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
      simp [bivariateToParametric, parametricToBivariate]

theorem bivariateToParametric_injective : Function.Injective bivariateToParametric := by
  apply Function.LeftInverse.injective (g := parametricToBivariate)
  intro q
  exact DFunLike.congr_fun parametricToBivariate_comp_bivariateToParametric q

theorem bivariateToParametric_eval (q : MvPolynomial (Unit ⊕ Unit) ℝ) (P t : ℝ) :
    (bivariateToParametric q).eval₂ (Polynomial.evalRingHom P) t =
      MvPolynomial.eval (polynomialGraphCoordinates (fun _ => P) t) q := by
  have he : (Polynomial.eval₂RingHom (Polynomial.evalRingHom P) t).comp
      bivariateToParametric =
      MvPolynomial.eval (polynomialGraphCoordinates (fun _ => P) t) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [bivariateToParametric]
    · intro i
      rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
        simp [bivariateToParametric, polynomialGraphCoordinates]
  exact DFunLike.congr_fun he q

theorem bivariate_polynomial_positive_roots_threshold_lower
    (q : MvPolynomial (Unit ⊕ Unit) ℝ) (hq : q ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∃ T : ℝ, 2 ≤ T ∧
      ∀ P : ℝ, T ≤ P → ∀ t : ℝ, 0 < t →
        MvPolynomial.eval (polynomialGraphCoordinates (fun _ => P) t) q = 0 →
          c / P ^ N ≤ t := by
  have hn : bivariateToParametric q ≠ 0 := by
    intro h
    exact hq (bivariateToParametric_injective (h.trans (map_zero _).symm))
  rcases parametric_polynomial_positive_roots_threshold_lower (bivariateToParametric q) hn with
    ⟨c, hc, N, T, hT, hbound⟩
  exact ⟨c, hc, N, T, hT, fun P hP t ht hr =>
    hbound P hP t ht (by rwa [bivariateToParametric_eval])⟩

end PaperI
