import PaperILean.DirectionalPolynomialDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators

/-! Exact finite Taylor reconstruction along affine lines. The polynomial
restriction preserves the full parent degree bound, including constants.
-/

open scoped BigOperators
noncomputable section
namespace PaperI

def polynomialAlongLine (P : MvPolynomial (Fin 3) ℝ) (c v : PhysicalSpace) :
    Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (c i) + Polynomial.C (v i) * Polynomial.X) P

theorem eval_polynomialAlongLine (P : MvPolynomial (Fin 3) ℝ)
    (c v : PhysicalSpace) (t : ℝ) :
    (polynomialAlongLine P c v).eval t = MvPolynomial.eval (c + t • v) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [polynomialAlongLine]
  | add P Q hP hQ => simpa [polynomialAlongLine] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
      simp only [polynomialAlongLine, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
        Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
        map_mul, MvPolynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
      rw [hP, mul_comm (v i) t]

theorem natDegree_polynomialAlongLine_le (P : MvPolynomial (Fin 3) ℝ)
    (c v : PhysicalSpace) :
    (polynomialAlongLine P c v).natDegree ≤ P.totalDegree := by
  classical
  unfold polynomialAlongLine
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  have hvar (i : Fin 3) :
      (Polynomial.C (c i) + Polynomial.C (v i) * Polynomial.X).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le (v i) 1
  have hsum : ∑ i : Fin 3,
      ((Polynomial.C (c i) + Polynomial.C (v i) * Polynomial.X) ^ e i).natDegree ≤
        ∑ i : Fin 3, e i := by
    apply Finset.sum_le_sum
    intro i hi
    exact (Polynomial.natDegree_pow_le).trans
      (by simpa only [mul_one] using Nat.mul_le_mul_left (e i) (hvar i))
  apply hsum.trans
  have hd := MvPolynomial.le_totalDegree he
  rw [Finsupp.sum_fintype e (fun _ n => n) (by intro i; rfl)] at hd
  exact hd

theorem iteratedDeriv_polynomial_eval (n : ℕ) (q : Polynomial ℝ) :
    iteratedDeriv n (fun t : ℝ => q.eval t) =
      fun t => (Polynomial.derivative^[n] q).eval t := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      simpa only [Function.iterate_succ_apply'] using
        (Polynomial.derivative^[n] q).deriv (x := t)

theorem iteratedDeriv_polynomial_eval_zero (n : ℕ) (q : Polynomial ℝ) :
    iteratedDeriv n (fun t : ℝ => q.eval t) 0 = (n.factorial : ℝ) * q.coeff n := by
  rw [iteratedDeriv_polynomial_eval]
  dsimp only
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp [
    Nat.descFactorial_self, nsmul_eq_mul]

theorem polynomial_eval_one_taylor (q : Polynomial ℝ) (k : ℕ)
    (hq : q.natDegree ≤ k) :
    q.eval 1 = ∑ n ∈ Finset.range (k + 1),
      (n.factorial : ℝ)⁻¹ * iteratedDeriv n (fun t : ℝ => q.eval t) 0 := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [iteratedDeriv_polynomial_eval_zero]
  simp [Nat.factorial_ne_zero, mul_assoc]

theorem iteratedDeriv_evalPolynomial_line (P : MvPolynomial (Fin 3) ℝ)
    (c v : PhysicalSpace) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => MvPolynomial.eval (c + t • v) P) 0 =
      iteratedFDeriv ℝ n (fun x : PhysicalSpace => MvPolynomial.eval x P) c
        (fun _ => v) := by
  let L : ℝ →L[ℝ] PhysicalSpace := (1 : ℝ →L[ℝ] ℝ).smulRight v
  have heq : (fun t : ℝ => MvPolynomial.eval (c + t • v) P) =
      (fun x : PhysicalSpace => MvPolynomial.eval (c + x) P) ∘ L := by
    funext t
    simp [L]
  have hc : ContDiff ℝ (n : WithTop ℕ∞)
      (fun x : PhysicalSpace => MvPolynomial.eval (c + x) P) :=
    (contDiff_evalPolynomial P (n : WithTop ℕ∞)).comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv, heq,
    L.iteratedFDeriv_comp_right (i := n) hc (0 : ℝ) le_rfl]
  have hs := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
    (f := fun y : PhysicalSpace => MvPolynomial.eval y P) n c (L 0)
  have hh := congrArg (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin n => PhysicalSpace) ℝ =>
    M.compContinuousLinearMap (fun _ => L) (fun _ => (1 : ℝ))) hs
  exact hh.trans (by simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, L])

theorem evalPolynomial_finite_taylor (P : MvPolynomial (Fin 3) ℝ)
    (k : ℕ) (hP : P.totalDegree ≤ k) (c v : PhysicalSpace) :
    MvPolynomial.eval (c + v) P = ∑ n ∈ Finset.range (k + 1),
      (n.factorial : ℝ)⁻¹ *
        iteratedFDeriv ℝ n (fun x : PhysicalSpace => MvPolynomial.eval x P) c (fun _ => v) := by
  have hq := polynomial_eval_one_taylor (polynomialAlongLine P c v) k
    ((natDegree_polynomialAlongLine_le P c v).trans hP)
  have heq : (fun t : ℝ => (polynomialAlongLine P c v).eval t) =
      (fun t : ℝ => MvPolynomial.eval (c + t • v) P) := by
    funext t
    exact eval_polynomialAlongLine P c v t
  rw [heq] at hq
  simpa only [eval_polynomialAlongLine, one_smul,
    iteratedDeriv_evalPolynomial_line] using hq

end PaperI
