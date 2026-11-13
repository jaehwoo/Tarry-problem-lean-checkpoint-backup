import PaperILean.IteratedPolynomialDerivatives
import Mathlib.Data.Nat.Factorial.Basic

/-! Algebraic coefficient recovery for partial derivatives. The shift factor is
the coordinate exponent, not a total-degree factorial. These are full-parent
polynomial identities; constants and zero exponents remain in the domain.
-/

noncomputable section
namespace PaperI

theorem coeff_polynomialPartial (i : Fin 3) (e : Fin 3 →₀ ℕ)
    (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.coeff e (MvPolynomial.pderiv i P) =
      ((e i + 1 : ℕ) : ℝ) * MvPolynomial.coeff (e + Finsupp.single i 1) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
      rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial]
      by_cases hd : d i = 0
      · have he : d ≠ e + Finsupp.single i 1 := by
          intro he
          have h := congrArg (fun q : Fin 3 →₀ ℕ => q i) he
          simp [hd] at h
        simp [hd, he]
      · have hadd : d - Finsupp.single i 1 + Finsupp.single i 1 = d :=
          Finsupp.sub_add_single_one_cancel hd
        by_cases he : d = e + Finsupp.single i 1
        · have hsub : d - Finsupp.single i 1 = e := by
            rw [he]
            exact add_tsub_cancel_right e (Finsupp.single i 1)
          have hv : d i = e i + 1 := by rw [he]; simp
          simp [he, hsub, hv, mul_comm]
        · have hsub : d - Finsupp.single i 1 ≠ e := by
            intro h
            rw [h] at hadd
            exact he hadd.symm
          simp [he, hsub]
  | add P Q hP hQ =>
      simp only [map_add, MvPolynomial.coeff_add, hP, hQ, mul_add]

theorem constantCoeff_polynomialPartial (i : Fin 3) (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.coeff 0 (MvPolynomial.pderiv i P) =
      MvPolynomial.coeff (Finsupp.single i 1) P := by
  simpa using coeff_polynomialPartial i 0 P

theorem fderiv_evalPolynomial_zero_single (P : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    fderiv ℝ (fun y : PhysicalSpace => MvPolynomial.eval y P) 0
      (Pi.single i (1 : ℝ)) = MvPolynomial.coeff (Finsupp.single i 1) P := by
  rw [fderiv_evalPolynomial_single, MvPolynomial.eval_zero]
  exact constantCoeff_polynomialPartial i P

def repeatedPolynomialPartial (i : Fin 3) : ℕ →
    MvPolynomial (Fin 3) ℝ → MvPolynomial (Fin 3) ℝ
  | 0, P => P
  | n + 1, P => repeatedPolynomialPartial i n (MvPolynomial.pderiv i P)

theorem coeff_repeatedPolynomialPartial (i : Fin 3) (n : ℕ)
    (e : Fin 3 →₀ ℕ) (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.coeff e (repeatedPolynomialPartial i n P) =
      (((e i + 1).ascFactorial n : ℕ) : ℝ) *
        MvPolynomial.coeff (e + Finsupp.single i n) P := by
  induction n generalizing P with
  | zero => simp [repeatedPolynomialPartial]
  | succ n ih =>
      rw [repeatedPolynomialPartial, ih, coeff_polynomialPartial]
      have hshift : e + Finsupp.single i n + Finsupp.single i 1 =
          e + Finsupp.single i (n + 1) := by
        rw [add_assoc, ← Finsupp.single_add]
      rw [hshift, Nat.ascFactorial_succ, Nat.cast_mul]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
      ring

def coordinatePolynomialPartial (e : Fin 3 →₀ ℕ) (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  repeatedPolynomialPartial 2 (e 2)
    (repeatedPolynomialPartial 1 (e 1) (repeatedPolynomialPartial 0 (e 0) P))

theorem exponent_eq_three_singles (e : Fin 3 →₀ ℕ) :
    Finsupp.single 2 (e 2) + Finsupp.single 1 (e 1) + Finsupp.single 0 (e 0) = e := by
  ext i
  fin_cases i <;> simp

theorem constantCoeff_coordinatePolynomialPartial (e : Fin 3 →₀ ℕ)
    (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.coeff 0 (coordinatePolynomialPartial e P) =
      ((e 2).factorial : ℝ) * ((e 1).factorial : ℝ) * ((e 0).factorial : ℝ) *
        MvPolynomial.coeff e P := by
  unfold coordinatePolynomialPartial
  rw [coeff_repeatedPolynomialPartial, coeff_repeatedPolynomialPartial,
    coeff_repeatedPolynomialPartial]
  simp only [zero_add]
  rw [exponent_eq_three_singles]
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  norm_num [Finsupp.add_apply, Finsupp.single_apply, h21, h20, h10, mul_assoc]

end PaperI
