import PaperILean.OriginalBivariatePolynomialJacobian
import PaperILean.RealPolynomialDefinability
import Mathlib.Algebra.MvPolynomial.Funext

/-! The joint polynomial nonsingular-root relation, with every external
coordinate retained and only the two output coordinates differentiated. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def jointBivariateSpecialize {ρ : Type} (P : MvPolynomial (ρ ⊕ Fin 2) ℝ) (a : ρ → ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim (MvPolynomial.C ∘ a) MvPolynomial.X) P

theorem jointBivariateSpecialize_eval {ρ : Type} (P : MvPolynomial (ρ ⊕ Fin 2) ℝ)
    (a : ρ → ℝ) (w : Fin 2 → ℝ) :
    MvPolynomial.eval w (jointBivariateSpecialize P a) = MvPolynomial.eval (Sum.elim a w) P := by
  change MvPolynomial.eval w (MvPolynomial.eval₂ MvPolynomial.C _ P) = _
  rw [← MvPolynomial.eval_assoc]
  congr 2
  funext i
  cases i <;> simp

theorem jointBivariateSpecialize_pderiv {ρ : Type} (P : MvPolynomial (ρ ⊕ Fin 2) ℝ)
    (a : ρ → ℝ) (i : Fin 2) :
    MvPolynomial.pderiv i (jointBivariateSpecialize P a) =
      jointBivariateSpecialize (MvPolynomial.pderiv (Sum.inr i) P) a := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [jointBivariateSpecialize,MvPolynomial.pderiv_C]
  | add P Q hP hQ => simpa only [jointBivariateSpecialize,map_add] using congrArg₂ (·+·) hP hQ
  | mul_X P j hP =>
    cases j with
    | inl r => simp [jointBivariateSpecialize,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,
        Pi.single_apply,Function.comp_def] at hP ⊢; rw [hP]; simp
    | inr j => simp [jointBivariateSpecialize,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,
        Pi.single_apply] at hP ⊢; rw [hP]; by_cases h : j=i <;> simp [h]

def jointBivariateJacobianPolynomial {ρ : Type} (P Q : MvPolynomial (ρ ⊕ Fin 2) ℝ) :
    MvPolynomial (ρ ⊕ Fin 2) ℝ :=
  MvPolynomial.pderiv (Sum.inr 0) P * MvPolynomial.pderiv (Sum.inr 1) Q -
    MvPolynomial.pderiv (Sum.inr 1) P * MvPolynomial.pderiv (Sum.inr 0) Q

theorem jointBivariateJacobianPolynomial_eval {ρ : Type}
    (P Q : MvPolynomial (ρ ⊕ Fin 2) ℝ) (a : ρ → ℝ) (w : Fin 2 → ℝ) :
    MvPolynomial.eval (Sum.elim a w) (jointBivariateJacobianPolynomial P Q) =
      (originalBivariateJacobian (jointBivariateSpecialize P a) (jointBivariateSpecialize Q a) w).det := by
  simp only [jointBivariateJacobianPolynomial,map_sub,map_mul,originalBivariateJacobian,
    Matrix.det_fin_two,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
    jointBivariateSpecialize_pderiv,jointBivariateSpecialize_eval]

def jointBivariateRegularRelation {ρ : Type} (P Q : MvPolynomial (ρ ⊕ Fin 2) ℝ) :
    Set ((ρ ⊕ Fin 2) → ℝ) :=
  {v | MvPolynomial.eval v P=0 ∧ MvPolynomial.eval v Q=0 ∧
    MvPolynomial.eval v (jointBivariateJacobianPolynomial P Q)≠0}

theorem jointBivariateRegularRelation_definable {ρ : Type}
    (P Q : MvPolynomial (ρ ⊕ Fin 2) ℝ) :
    (univ : Set ℝ).Definable Language.ring (jointBivariateRegularRelation P Q) :=
  (realPolynomial_zero_definable P).inter
    ((realPolynomial_zero_definable Q).inter (realPolynomial_zero_definable _).compl)

end PaperI
