import PaperILean.PolynomialDerivativeCoefficients
import PaperILean.AffineJetDerivatives

/-! Mixed monomial coefficients are recovered from actual derivative tensors.
Slots are listed in the order 2,1,0, with each coordinate repeated according to
its exponent. The factor is the product of the three coordinate factorials.
The order-zero case is kept for arbitrary polynomials; the normalized affine
identity is restricted to nonzero exponents as in the nonconstant jet.
-/

noncomputable section
open Matrix
namespace PaperI

def listPolynomialPartial : List (Fin 3) →
    MvPolynomial (Fin 3) ℝ → MvPolynomial (Fin 3) ℝ
  | [], P => P
  | i :: l, P => MvPolynomial.pderiv i (listPolynomialPartial l P)

theorem listPolynomialPartial_append (l m : List (Fin 3))
    (P : MvPolynomial (Fin 3) ℝ) :
    listPolynomialPartial (l ++ m) P = listPolynomialPartial l (listPolynomialPartial m P) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [listPolynomialPartial, ih]

theorem polynomialPartial_repeated (i : Fin 3) (n : ℕ) (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv i (repeatedPolynomialPartial i n P) =
      repeatedPolynomialPartial i n (MvPolynomial.pderiv i P) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
      change MvPolynomial.pderiv i (repeatedPolynomialPartial i n (MvPolynomial.pderiv i P)) =
        repeatedPolynomialPartial i n (MvPolynomial.pderiv i (MvPolynomial.pderiv i P))
      exact ih (MvPolynomial.pderiv i P)

theorem listPolynomialPartial_replicate (i : Fin 3) (n : ℕ)
    (P : MvPolynomial (Fin 3) ℝ) :
    listPolynomialPartial (List.replicate n i) P = repeatedPolynomialPartial i n P := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, listPolynomialPartial, ih, polynomialPartial_repeated]
      rfl

theorem listPolynomialPartial_eq_iterated (l : List (Fin 3))
    (P : MvPolynomial (Fin 3) ℝ) :
    listPolynomialPartial l P = iteratedPolynomialPartial l.length l.get P := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      change MvPolynomial.pderiv i (listPolynomialPartial l P) =
        MvPolynomial.pderiv i (iteratedPolynomialPartial l.length l.get P)
      rw [ih]

def coordinateDerivativeOrder (e : Fin 3 →₀ ℕ) : List (Fin 3) :=
  List.replicate (e 2) 2 ++ (List.replicate (e 1) 1 ++ List.replicate (e 0) 0)

theorem listPolynomialPartial_coordinateOrder (e : Fin 3 →₀ ℕ)
    (P : MvPolynomial (Fin 3) ℝ) :
    listPolynomialPartial (coordinateDerivativeOrder e) P = coordinatePolynomialPartial e P := by
  simp only [coordinateDerivativeOrder, listPolynomialPartial_append,
    listPolynomialPartial_replicate, coordinatePolynomialPartial]

theorem coordinateDerivativeOrder_length (e : Fin 3 →₀ ℕ) :
    (coordinateDerivativeOrder e).length = e.sum (fun _ n => n) := by
  simp only [coordinateDerivativeOrder, List.length_append, List.length_replicate]
  rw [Finsupp.sum_fintype _ _ (by intro i; rfl)]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
    Fin.succ_zero_eq_one, add_zero]
  change e 2 + (e 1 + e 0) = e 0 + (e 1 + e 2)
  omega

theorem coordinateDerivativeOrder_length_ne_zero (e : Fin 3 →₀ ℕ) (he : e ≠ 0) :
    (coordinateDerivativeOrder e).length ≠ 0 := by
  intro h
  have hsum : e 2 + (e 1 + e 0) = 0 := by
    simpa only [coordinateDerivativeOrder, List.length_append, List.length_replicate] using h
  apply he
  ext i
  fin_cases i
  · change e 0 = 0
    omega
  · change e 1 = 0
    omega
  · change e 2 = 0
    omega

theorem iteratedFDeriv_evalPolynomial_mixed_zero (e : Fin 3 →₀ ℕ)
    (P : MvPolynomial (Fin 3) ℝ) :
    iteratedFDeriv ℝ (coordinateDerivativeOrder e).length
      (fun y : PhysicalSpace => MvPolynomial.eval y P) 0
      (fun j => Pi.single ((coordinateDerivativeOrder e).get j) (1 : ℝ)) =
      ((e 2).factorial : ℝ) * ((e 1).factorial : ℝ) * ((e 0).factorial : ℝ) *
        MvPolynomial.coeff e P := by
  rw [iteratedFDeriv_evalPolynomial_coordinate,
    ← listPolynomialPartial_eq_iterated, listPolynomialPartial_coordinateOrder,
    MvPolynomial.eval_zero]
  exact constantCoeff_coordinatePolynomialPartial e P

theorem iteratedFDeriv_phase_mixed_zero {k : ℕ} (F : CoefficientSpace k) (e : Fin 3 →₀ ℕ) :
    iteratedFDeriv ℝ (coordinateDerivativeOrder e).length (phase F) 0
      (fun j => Pi.single ((coordinateDerivativeOrder e).get j) (1 : ℝ)) =
      ((e 2).factorial : ℝ) * ((e 1).factorial : ℝ) * ((e 0).factorial : ℝ) *
        MvPolynomial.coeff e (coefficientPolynomial F) := by
  simpa only [eval_coefficientPolynomial] using
    iteratedFDeriv_evalPolynomial_mixed_zero e (coefficientPolynomial F)

theorem iteratedFDeriv_phase_affine_zero_nonzero (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k)
    (n : ℕ) (hn : n ≠ 0) (v : Fin n → PhysicalSpace) :
    iteratedFDeriv ℝ n (phase (affineCoefficientMap k c B F)) 0 v =
      iteratedFDeriv ℝ n (phase F) c (fun j => B *ᵥ v j) := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n => exact iteratedFDeriv_phase_affine_zero_positive k c B F n v

theorem affineJet_mixed_coefficient (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k)
    (e : Fin 3 →₀ ℕ) (he : e ≠ 0) :
    iteratedFDeriv ℝ (coordinateDerivativeOrder e).length (phase F) c
      (fun j => B *ᵥ Pi.single ((coordinateDerivativeOrder e).get j) (1 : ℝ)) =
      ((e 2).factorial : ℝ) * ((e 1).factorial : ℝ) * ((e 0).factorial : ℝ) *
        MvPolynomial.coeff e (coefficientPolynomial (affineCoefficientMap k c B F)) := by
  rw [← iteratedFDeriv_phase_affine_zero_nonzero k c B F _
    (coordinateDerivativeOrder_length_ne_zero e he)]
  exact iteratedFDeriv_phase_mixed_zero (affineCoefficientMap k c B F) e

end PaperI
