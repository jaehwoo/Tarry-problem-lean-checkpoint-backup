import PaperILean.IteratedPolynomialDerivatives
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-! The actual polynomial derivative tensors are symmetric at every order.
Polynomial analyticity is proved by structural induction; it is not imposed
as an additional hypothesis. The amplitude smoothness target is unchanged.
-/

noncomputable section
namespace PaperI

theorem iteratedFDeriv_evalPolynomial_perm (P : MvPolynomial (Fin 3) ℝ)
    (n : ℕ) (x : PhysicalSpace) (v : Fin n → PhysicalSpace) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n (fun y : PhysicalSpace => MvPolynomial.eval y P) x (v ∘ σ) =
      iteratedFDeriv ℝ n (fun y : PhysicalSpace => MvPolynomial.eval y P) x v :=
  (contDiff_evalPolynomial P (⊤ : WithTop ℕ∞)).contDiffAt.iteratedFDeriv_comp_perm v σ

theorem iteratedFDeriv_phase_perm {k : ℕ} (F : CoefficientSpace k)
    (n : ℕ) (x : PhysicalSpace) (v : Fin n → PhysicalSpace) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n (phase F) x (v ∘ σ) = iteratedFDeriv ℝ n (phase F) x v :=
  (contDiff_phase F (⊤ : WithTop ℕ∞)).contDiffAt.iteratedFDeriv_comp_perm v σ

end PaperI
