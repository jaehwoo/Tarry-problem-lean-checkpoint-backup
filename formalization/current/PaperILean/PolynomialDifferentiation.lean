import PaperILean.CoefficientModel
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! The algebraic partial derivatives are the actual Fréchet derivatives of
the evaluated polynomial. This supplies a derivative bridge for the complete
jet at main manuscript lines 161–176; it does not yet prove the higher tensor
Taylor formula or the Hilbert–Schmidt coefficient-window estimate.

The proofs use structural polynomial induction. They apply to the full parent
polynomial, including constants and all degrees, without rank assumptions.
-/

open scoped BigOperators

noncomputable section
namespace PaperI

def polynomialDifferential (P : MvPolynomial (Fin 3) ℝ) (x : PhysicalSpace) :
    PhysicalSpace →L[ℝ] ℝ :=
  ∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i P)) • ContinuousLinearMap.proj i

theorem polynomialDifferential_apply (P : MvPolynomial (Fin 3) ℝ)
    (x v : PhysicalSpace) :
    polynomialDifferential P x v =
      ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) * v i := by
  simp [polynomialDifferential, ContinuousLinearMap.sum_apply]

theorem polynomialDifferential_C (a : ℝ) (x : PhysicalSpace) :
    polynomialDifferential (MvPolynomial.C a) x = 0 := by
  simp [polynomialDifferential, MvPolynomial.pderiv_C]

theorem polynomialDifferential_add (P Q : MvPolynomial (Fin 3) ℝ)
    (x : PhysicalSpace) :
    polynomialDifferential (P + Q) x =
      polynomialDifferential P x + polynomialDifferential Q x := by
  simp [polynomialDifferential, add_smul, Finset.sum_add_distrib]

theorem polynomialDifferential_mul_X (P : MvPolynomial (Fin 3) ℝ)
    (j : Fin 3) (x : PhysicalSpace) :
    polynomialDifferential (P * MvPolynomial.X j) x =
      (MvPolynomial.eval x P) • ContinuousLinearMap.proj j +
        (x j) • polynomialDifferential P x := by
  ext v
  simp only [polynomialDifferential_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.eval_X]
  simp [MvPolynomial.pderiv_X, Pi.single_apply, Finset.sum_add_distrib,
    Finset.mul_sum, mul_add, mul_assoc, mul_comm, mul_left_comm, add_comm]

theorem contDiff_evalPolynomial (P : MvPolynomial (Fin 3) ℝ)
    (n : WithTop ℕ∞) : ContDiff ℝ n (fun x : PhysicalSpace => MvPolynomial.eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ n (fun _ : PhysicalSpace => a))
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P j hP => simpa using hP.mul (contDiff_apply ℝ ℝ j)

theorem hasFDerivAt_evalPolynomial (P : MvPolynomial (Fin 3) ℝ)
    (x : PhysicalSpace) :
    HasFDerivAt (fun y : PhysicalSpace => MvPolynomial.eval y P)
      (polynomialDifferential P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simpa [polynomialDifferential_C] using (hasFDerivAt_const a x)
  | add P Q hP hQ =>
      simpa [polynomialDifferential_add] using hP.add hQ
  | mul_X P j hP =>
      simpa [polynomialDifferential_mul_X] using hP.mul (hasFDerivAt_apply j x)

theorem fderiv_evalPolynomial (P : MvPolynomial (Fin 3) ℝ)
    (x : PhysicalSpace) :
    fderiv ℝ (fun y : PhysicalSpace => MvPolynomial.eval y P) x =
      polynomialDifferential P x :=
  (hasFDerivAt_evalPolynomial P x).fderiv

theorem fderiv_evalPolynomial_apply (P : MvPolynomial (Fin 3) ℝ)
    (x v : PhysicalSpace) :
    fderiv ℝ (fun y : PhysicalSpace => MvPolynomial.eval y P) x v =
      ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) * v i := by
  rw [fderiv_evalPolynomial, polynomialDifferential_apply]

theorem fderiv_evalPolynomial_single (P : MvPolynomial (Fin 3) ℝ)
    (x : PhysicalSpace) (j : Fin 3) :
    fderiv ℝ (fun y : PhysicalSpace => MvPolynomial.eval y P) x
      (Pi.single j (1 : ℝ)) = MvPolynomial.eval x (MvPolynomial.pderiv j P) := by
  rw [fderiv_evalPolynomial_apply]
  simp [Pi.single_apply]

theorem contDiff_phase {k : ℕ} (F : CoefficientSpace k) (n : WithTop ℕ∞) :
    ContDiff ℝ n (phase F) := by
  simpa only [eval_coefficientPolynomial] using
    contDiff_evalPolynomial (coefficientPolynomial F) n

theorem hasFDerivAt_phase {k : ℕ} (F : CoefficientSpace k) (x : PhysicalSpace) :
    HasFDerivAt (phase F) (polynomialDifferential (coefficientPolynomial F) x) x := by
  simpa only [eval_coefficientPolynomial] using
    hasFDerivAt_evalPolynomial (coefficientPolynomial F) x

end PaperI
