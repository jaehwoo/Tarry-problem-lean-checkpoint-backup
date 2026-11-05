import PaperILean.PolynomialDerivativeCoefficients

/-! Algebraic directional derivatives on the full polynomial parent. Degree
bounds include zero and constant polynomials. No analytic or rank assumption
is imposed. Ordered directions agree with actual iterated Fréchet derivatives.
-/

open scoped BigOperators
noncomputable section
namespace PaperI

def directionalPolynomialPartial (v : PhysicalSpace)
    (P : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i, v i • MvPolynomial.pderiv i P

theorem eval_directionalPolynomialPartial (v x : PhysicalSpace)
    (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.eval x (directionalPolynomialPartial v P) =
      fderiv ℝ (fun y : PhysicalSpace => MvPolynomial.eval y P) x v := by
  rw [fderiv_evalPolynomial_apply]
  simp [directionalPolynomialPartial, MvPolynomial.eval_sum, mul_comm]

theorem totalDegree_polynomialPartial_le (i : Fin 3)
    (P : MvPolynomial (Fin 3) ℝ) :
    (MvPolynomial.pderiv i P).totalDegree ≤ P.totalDegree - 1 := by
  classical
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro e he
  have hc : MvPolynomial.coeff (e + Finsupp.single i 1) P ≠ 0 := by
    intro hc
    have hh := MvPolynomial.mem_support_iff.mp he
    rw [coeff_polynomialPartial, hc, mul_zero] at hh
    exact hh rfl
  have hd := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  have hs : (e + Finsupp.single i 1).sum (fun _ n => n) =
      e.sum (fun _ n => n) + 1 := by
    rw [Finsupp.sum_fintype _ _ (by intro j; rfl),
      Finsupp.sum_fintype _ _ (by intro j; rfl)]
    simp [Finset.sum_add_distrib]
  rw [hs] at hd
  omega

theorem totalDegree_directionalPolynomialPartial_le (v : PhysicalSpace)
    (P : MvPolynomial (Fin 3) ℝ) :
    (directionalPolynomialPartial v P).totalDegree ≤ P.totalDegree - 1 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_smul_le (v i) _).trans
    (totalDegree_polynomialPartial_le i P)

def iteratedDirectionalPolynomialPartial : (n : ℕ) → (Fin n → PhysicalSpace) →
    MvPolynomial (Fin 3) ℝ → MvPolynomial (Fin 3) ℝ
  | 0, _, P => P
  | n + 1, v, P => directionalPolynomialPartial (v 0)
      (iteratedDirectionalPolynomialPartial n (Fin.tail v) P)

theorem iteratedFDeriv_evalPolynomial_directions (n : ℕ)
    (P : MvPolynomial (Fin 3) ℝ) (x : PhysicalSpace) (v : Fin n → PhysicalSpace) :
    iteratedFDeriv ℝ n (fun y : PhysicalSpace => MvPolynomial.eval y P) x v =
      MvPolynomial.eval x (iteratedDirectionalPolynomialPartial n v P) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hc : DifferentiableAt ℝ
          (iteratedFDeriv ℝ n (fun y : PhysicalSpace => MvPolynomial.eval y P)) x := by
        apply (ContDiff.differentiable_iteratedFDeriv
          (n := ((n + 1 : ℕ) : WithTop ℕ∞)) (m := n)
          (by exact_mod_cast Nat.lt_succ_self n)
          (contDiff_evalPolynomial P ((n + 1 : ℕ) : WithTop ℕ∞))).differentiableAt
      have heq : (fun y : PhysicalSpace =>
          iteratedFDeriv ℝ n (fun z : PhysicalSpace => MvPolynomial.eval z P) y (Fin.tail v)) =
          (fun y : PhysicalSpace => MvPolynomial.eval y
            (iteratedDirectionalPolynomialPartial n (Fin.tail v) P)) := by
        funext y
        exact ih y (Fin.tail v)
      rw [iteratedFDeriv_succ_apply_left]
      change (fderiv ℝ
        (iteratedFDeriv ℝ n (fun y : PhysicalSpace => MvPolynomial.eval y P)) x
          (v 0)) (Fin.tail v) = _
      rw [← fderiv_continuousMultilinear_apply_const_apply hc, heq]
      exact (eval_directionalPolynomialPartial (v 0) x _).symm

theorem totalDegree_iteratedDirectionalPolynomialPartial_le (n : ℕ)
    (v : Fin n → PhysicalSpace) (P : MvPolynomial (Fin 3) ℝ) :
    (iteratedDirectionalPolynomialPartial n v P).totalDegree ≤ P.totalDegree - n := by
  induction n with
  | zero => simp [iteratedDirectionalPolynomialPartial]
  | succ n ih =>
      exact (totalDegree_directionalPolynomialPartial_le _ _).trans
        (by simpa only [Nat.sub_sub] using Nat.sub_le_sub_right (ih (Fin.tail v)) 1)

def prependDirections : (m n : ℕ) → (Fin m → PhysicalSpace) →
    (Fin n → PhysicalSpace) → (Fin (n + m) → PhysicalSpace)
  | 0, _, _, w => w
  | m + 1, n, v, w => Fin.cons (v 0) (prependDirections m n (Fin.tail v) w)

theorem iteratedDirectionalPolynomialPartial_prepend (m n : ℕ)
    (v : Fin m → PhysicalSpace) (w : Fin n → PhysicalSpace)
    (P : MvPolynomial (Fin 3) ℝ) :
    iteratedDirectionalPolynomialPartial (n + m) (prependDirections m n v w) P =
      iteratedDirectionalPolynomialPartial m v
        (iteratedDirectionalPolynomialPartial n w P) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [prependDirections, iteratedDirectionalPolynomialPartial,
        Fin.cons_zero, Fin.tail_cons]
      exact congrArg (directionalPolynomialPartial (v 0)) (ih (Fin.tail v))

end PaperI
