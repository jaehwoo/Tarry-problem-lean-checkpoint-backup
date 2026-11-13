import PaperILean.PolynomialDifferentiation

/-! Ordered algebraic partial derivatives agree with the actual multilinear
Fréchet derivatives, at every order. No restriction to a low-degree slice is
made. This does not yet assert tensor symmetry, factorial coefficient recovery,
or an equivalence with Hilbert–Schmidt norms.
-/

noncomputable section
namespace PaperI

def iteratedPolynomialPartial : (n : ℕ) → (Fin n → Fin 3) →
    MvPolynomial (Fin 3) ℝ → MvPolynomial (Fin 3) ℝ
  | 0, _, P => P
  | n + 1, a, P => MvPolynomial.pderiv (a 0) (iteratedPolynomialPartial n (Fin.tail a) P)

theorem iteratedFDeriv_evalPolynomial_coordinate (n : ℕ)
    (P : MvPolynomial (Fin 3) ℝ) (x : PhysicalSpace) (a : Fin n → Fin 3) :
    iteratedFDeriv ℝ n (fun y : PhysicalSpace => MvPolynomial.eval y P) x
      (fun j => Pi.single (a j) (1 : ℝ)) =
        MvPolynomial.eval x (iteratedPolynomialPartial n a P) := by
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
          iteratedFDeriv ℝ n (fun z : PhysicalSpace => MvPolynomial.eval z P) y
            (fun j => Pi.single (Fin.tail a j) (1 : ℝ))) =
          (fun y : PhysicalSpace => MvPolynomial.eval y
            (iteratedPolynomialPartial n (Fin.tail a) P)) := by
        funext y
        exact ih y (Fin.tail a)
      rw [iteratedFDeriv_succ_apply_left]
      change (fderiv ℝ
        (iteratedFDeriv ℝ n (fun y : PhysicalSpace => MvPolynomial.eval y P)) x
          (Pi.single (a 0) (1 : ℝ)))
          (fun j => Pi.single (Fin.tail a j) (1 : ℝ)) = _
      rw [← fderiv_continuousMultilinear_apply_const_apply hc, heq]
      exact fderiv_evalPolynomial_single _ x (a 0)

theorem iteratedFDeriv_phase_coordinate {k : ℕ} (F : CoefficientSpace k)
    (n : ℕ) (x : PhysicalSpace) (a : Fin n → Fin 3) :
    iteratedFDeriv ℝ n (phase F) x (fun j => Pi.single (a j) (1 : ℝ)) =
      MvPolynomial.eval x (iteratedPolynomialPartial n a (coefficientPolynomial F)) := by
  simpa only [eval_coefficientPolynomial] using
    iteratedFDeriv_evalPolynomial_coordinate n (coefficientPolynomial F) x a

theorem iteratedPolynomialPartial_add (n : ℕ) (a : Fin n → Fin 3)
    (P Q : MvPolynomial (Fin 3) ℝ) :
    iteratedPolynomialPartial n a (P + Q) =
      iteratedPolynomialPartial n a P + iteratedPolynomialPartial n a Q := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iteratedPolynomialPartial, ih, map_add]

theorem iteratedPolynomialPartial_C_succ (n : ℕ) (a : Fin (n + 1) → Fin 3) (c : ℝ) :
    iteratedPolynomialPartial (n + 1) a (MvPolynomial.C c) = 0 := by
  induction n with
  | zero => simp [iteratedPolynomialPartial, MvPolynomial.pderiv_C]
  | succ n ih =>
      rw [iteratedPolynomialPartial, ih]
      simp

theorem iteratedFDeriv_evalPolynomial_C_succ (n : ℕ) (a : Fin (n + 1) → Fin 3)
    (c : ℝ) (x : PhysicalSpace) :
    iteratedFDeriv ℝ (n + 1) (fun y : PhysicalSpace =>
      MvPolynomial.eval y (MvPolynomial.C c)) x
        (fun j => Pi.single (a j) (1 : ℝ)) = 0 := by
  rw [iteratedFDeriv_evalPolynomial_coordinate, iteratedPolynomialPartial_C_succ]
  simp

end PaperI
