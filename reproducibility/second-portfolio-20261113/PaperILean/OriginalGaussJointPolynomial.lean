import PaperILean.PublishedGaussRootCount
import PaperILean.RealPolynomialDefinability

/-! Polynomial dependence on every coefficient, not just on physical variables
with the phase fixed. The original normal derivative and both Gauss equations
are represented without additional vanishing or nondegeneracy assumptions. -/

noncomputable section
namespace PaperI
open scoped BigOperators

def originalPolynomialLinearFamily (k : ℕ)
    (L : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (MonomialIndex k ⊕ Fin 3) ℝ :=
  ∑ a, MvPolynomial.X (Sum.inl a) *
    MvPolynomial.rename Sum.inr (L (MvPolynomial.monomial (monomialExponent a) 1))

theorem originalPolynomialLinearFamily_eval {k : ℕ}
    (L : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ)
    (F : CoefficientSpace k) (x : PhysicalSpace) :
    MvPolynomial.eval (Sum.elim F x) (originalPolynomialLinearFamily k L) =
      MvPolynomial.eval x (L (coefficientPolynomial F)) := by
  have hs : coefficientPolynomial F =
      ∑ a, F a • MvPolynomial.monomial (monomialExponent a) (1 : ℝ) := by
    simpa only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one] using coefficientPolynomial_eq_sum F
  rw [hs]
  simp [originalPolynomialLinearFamily,map_sum,map_smul,MvPolynomial.eval_rename,Function.comp_def]

def originalNormalLinear : ℕ → MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ
  | 0 => LinearMap.id
  | n+1 => (MvPolynomial.pderiv 0).toLinearMap.comp (originalNormalLinear n)

theorem originalNormalLinear_apply (n : ℕ) (Q : MvPolynomial (Fin 3) ℝ) :
    originalNormalLinear n Q = iteratedPolynomialPartial n (fun _ => 0) Q := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (MvPolynomial.pderiv 0) ih

abbrev OriginalGaussParameters (k : ℕ) := MonomialIndex k ⊕ Fin 2

def originalGaussJointCoordinate {k : ℕ} :
    MonomialIndex k ⊕ Fin 3 → OriginalGaussParameters k ⊕ Fin 2 :=
  Sum.elim (fun a => Sum.inl (Sum.inl a)) ![Sum.inr 0,Sum.inr 1,Sum.inl (Sum.inr 1)]

def originalGaussJointLinearPolynomial (k : ℕ)
    (L : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (OriginalGaussParameters k ⊕ Fin 2) ℝ :=
  MvPolynomial.rename originalGaussJointCoordinate (originalPolynomialLinearFamily k L)

theorem originalGaussJointLinearPolynomial_eval {k : ℕ}
    (L : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ)
    (F : CoefficientSpace k) (p z : ℝ) (w : Fin 2 → ℝ) :
    MvPolynomial.eval (Sum.elim (Sum.elim F ![p,z]) w)
      (originalGaussJointLinearPolynomial k L) =
      MvPolynomial.eval ![w 0,w 1,z] (L (coefficientPolynomial F)) := by
  rw [originalGaussJointLinearPolynomial,MvPolynomial.eval_rename]
  have he : Sum.elim (Sum.elim F ![p,z]) w ∘ originalGaussJointCoordinate =
      Sum.elim F ![w 0,w 1,z] := by
    funext i
    cases i with
    | inl a => rfl
    | inr j => fin_cases j <;> rfl
  rw [he,originalPolynomialLinearFamily_eval]

def originalGaussJointFirstPolynomial (k n : ℕ) :
    MvPolynomial (OriginalGaussParameters k ⊕ Fin 2) ℝ :=
  originalGaussJointLinearPolynomial k (originalNormalLinear n)

def originalGaussJointPartialPolynomial (k n : ℕ) (i : Fin 3) :
    MvPolynomial (OriginalGaussParameters k ⊕ Fin 2) ℝ :=
  originalGaussJointLinearPolynomial k ((MvPolynomial.pderiv i).toLinearMap.comp (originalNormalLinear n))

def originalGaussJointSecondPolynomial (k n : ℕ) :
    MvPolynomial (OriginalGaussParameters k ⊕ Fin 2) ℝ :=
  originalGaussJointPartialPolynomial k n 1 +
    MvPolynomial.X (Sum.inl (Sum.inr 0)) * originalGaussJointPartialPolynomial k n 0

theorem originalGaussJointFirstPolynomial_eval {k : ℕ} (F : CoefficientSpace k)
    (n : ℕ) (p z : ℝ) (w : Fin 2 → ℝ) :
    MvPolynomial.eval (Sum.elim (Sum.elim F ![p,z]) w) (originalGaussJointFirstPolynomial k n) =
      originalNormalPhase F n ![w 0,w 1,z] := by
  rw [originalGaussJointFirstPolynomial,originalGaussJointLinearPolynomial_eval,
    originalNormalLinear_apply,originalNormalPhase_eq_eval]
  rfl

theorem originalGaussJointPartialPolynomial_eval {k : ℕ} (F : CoefficientSpace k)
    (n : ℕ) (i : Fin 3) (p z : ℝ) (w : Fin 2 → ℝ) :
    MvPolynomial.eval (Sum.elim (Sum.elim F ![p,z]) w) (originalGaussJointPartialPolynomial k n i) =
      MvPolynomial.eval ![w 0,w 1,z] (MvPolynomial.pderiv i (originalNormalPolynomial F n)) := by
  rw [originalGaussJointPartialPolynomial,originalGaussJointLinearPolynomial_eval]
  simp only [LinearMap.comp_apply,originalNormalLinear_apply]
  rfl

theorem originalGaussJointSecondPolynomial_eval {k : ℕ} (F : CoefficientSpace k)
    (n : ℕ) (p z : ℝ) (w : Fin 2 → ℝ) :
    MvPolynomial.eval (Sum.elim (Sum.elim F ![p,z]) w) (originalGaussJointSecondPolynomial k n) =
      MvPolynomial.eval ![w 0,w 1,z] (originalGaussSecondPolynomial F n p) := by
  simp [originalGaussJointSecondPolynomial,originalGaussJointPartialPolynomial_eval,
    originalGaussSecondPolynomial]

end PaperI
