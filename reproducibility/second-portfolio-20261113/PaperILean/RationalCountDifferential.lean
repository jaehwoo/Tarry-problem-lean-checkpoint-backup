import PaperILean.OriginalBivariatePolynomialJacobian
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! S515-S517: exact clearing of rational denominators and analytic Jacobians.
The input dimension is the manuscript's arbitrary k. No root count is assumed. -/
noncomputable section
open scoped BigOperators
namespace PaperI.RationalCount

def polynomialDifferential {k : ℕ} (P : MvPolynomial (Fin k) ℝ) (x : Fin k → ℝ) :
    (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) • ContinuousLinearMap.proj i

theorem polynomialDifferential_apply {k : ℕ} (P : MvPolynomial (Fin k) ℝ)
    (x v : Fin k → ℝ) :
    polynomialDifferential P x v = ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i P)*v i := by
  simp [polynomialDifferential,ContinuousLinearMap.sum_apply]

theorem polynomial_hasFDerivAt {k : ℕ} (P : MvPolynomial (Fin k) ℝ) (x : Fin k → ℝ) :
    HasFDerivAt (fun y => MvPolynomial.eval y P) (polynomialDifferential P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simpa [polynomialDifferential,MvPolynomial.pderiv_C] using (hasFDerivAt_const a x)
  | add P Q hP hQ =>
    have he : polynomialDifferential (P+Q) x =
        polynomialDifferential P x + polynomialDifferential Q x := by
      simp [polynomialDifferential,add_smul,Finset.sum_add_distrib]
    simpa [he] using hP.add hQ
  | mul_X P j hP =>
    have he : polynomialDifferential (P*MvPolynomial.X j) x =
        MvPolynomial.eval x P • ContinuousLinearMap.proj j + x j • polynomialDifferential P x := by
      ext v
      simp only [polynomialDifferential_apply,ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,
        MvPolynomial.pderiv_mul,map_add,map_mul,MvPolynomial.eval_X]
      simp [MvPolynomial.pderiv_X,Pi.single_apply,Finset.sum_add_distrib,
        Finset.mul_sum,mul_add,mul_assoc,mul_comm,mul_left_comm,add_comm]
    simpa [he] using hP.mul (hasFDerivAt_apply j x)

theorem polynomial_fderiv_single {k : ℕ} (P : MvPolynomial (Fin k) ℝ)
    (x : Fin k → ℝ) (j : Fin k) :
    fderiv ℝ (fun y => MvPolynomial.eval y P) x (Pi.single j 1) =
      MvPolynomial.eval x (MvPolynomial.pderiv j P) := by
  rw [(polynomial_hasFDerivAt P x).fderiv,polynomialDifferential_apply]
  simp [Pi.single_apply]

theorem polynomial_contDiff {k : ℕ} (P : MvPolynomial (Fin k) ℝ)
    (n : WithTop ℕ∞) : ContDiff ℝ n (fun x => MvPolynomial.eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ n (fun _ : Fin k → ℝ => a))
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P j hP => simpa using hP.mul (contDiff_apply ℝ ℝ j)

def polynomialMap {k : ℕ} (G : Fin k → MvPolynomial (Fin k) ℝ)
    (x : Fin k → ℝ) : Fin k → ℝ := fun i => MvPolynomial.eval x (G i)

def polynomialJacobian {k : ℕ} (G : Fin k → MvPolynomial (Fin k) ℝ)
    (x : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (G i))

theorem polynomialMap_contDiff {k : ℕ} (G : Fin k → MvPolynomial (Fin k) ℝ)
    (n : WithTop ℕ∞) : ContDiff ℝ n (polynomialMap G) := by
  exact contDiff_pi.mpr (fun i => polynomial_contDiff (G i) n)

theorem polynomialMap_hasFDerivAt {k : ℕ} (G : Fin k → MvPolynomial (Fin k) ℝ)
    (x : Fin k → ℝ) :
    HasFDerivAt (polynomialMap G)
      (ContinuousLinearMap.pi (fun i => polynomialDifferential (G i) x)) x := by
  exact hasFDerivAt_pi.mpr (fun i => polynomial_hasFDerivAt (G i) x)

theorem polynomialJacobian_mulVec {k : ℕ} (G : Fin k → MvPolynomial (Fin k) ℝ)
    (x v : Fin k → ℝ) :
    (polynomialJacobian G x).mulVec v =
      (ContinuousLinearMap.pi (fun i => polynomialDifferential (G i) x)) v := by
  funext i
  simp [polynomialJacobian,Matrix.mulVec,dotProduct,polynomialDifferential_apply]

def rationalMap {k : ℕ} (P Q : Fin k → MvPolynomial (Fin k) ℝ)
    (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i => MvPolynomial.eval x (P i) / MvPolynomial.eval x (Q i)

def rationalJacobian {k : ℕ} (P Q : Fin k → MvPolynomial (Fin k) ℝ)
    (x : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => fderiv ℝ (fun z => rationalMap P Q z i) x (Pi.single j 1)

def cleared {k : ℕ} (P Q : Fin k → MvPolynomial (Fin k) ℝ)
    (y : Fin k → ℝ) : Fin k → MvPolynomial (Fin k) ℝ :=
  fun i => P i - MvPolynomial.C (y i) * Q i

theorem rational_fderiv_single {k : ℕ} (P Q : MvPolynomial (Fin k) ℝ)
    (x : Fin k → ℝ) (j : Fin k) (hQ : MvPolynomial.eval x Q ≠ 0) :
    fderiv ℝ (fun z => MvPolynomial.eval z P / MvPolynomial.eval z Q) x (Pi.single j 1) =
      (MvPolynomial.eval x (MvPolynomial.pderiv j P) * MvPolynomial.eval x Q -
        MvPolynomial.eval x P * MvPolynomial.eval x (MvPolynomial.pderiv j Q)) /
          (MvPolynomial.eval x Q)^2 := by
  have hi := (hasFDerivAt_inv hQ).comp x (polynomial_hasFDerivAt Q x)
  have hd := ((polynomial_hasFDerivAt P x).mul hi).fderiv
  dsimp only [Function.comp_def] at hd
  have he : (fun z => MvPolynomial.eval z P / MvPolynomial.eval z Q) =
      (fun z => MvPolynomial.eval z P * (MvPolynomial.eval z Q)⁻¹) := by
    funext z
    exact div_eq_mul_inv _ _
  rw [he,hd]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply,smul_eq_mul,polynomialDifferential_apply]
  simp [Pi.single_apply]
  field_simp [hQ]
  <;> ring

theorem cleared_eval_zero {k : ℕ} (P Q : Fin k → MvPolynomial (Fin k) ℝ)
    (x y : Fin k → ℝ) (hQ : ∀ i, MvPolynomial.eval x (Q i) ≠ 0)
    (hxy : rationalMap P Q x = y) (i : Fin k) :
    MvPolynomial.eval x (cleared P Q y i) = 0 := by
  have hi : MvPolynomial.eval x (P i) / MvPolynomial.eval x (Q i) = y i := congrFun hxy i
  rw [div_eq_iff (hQ i)] at hi
  simp [cleared,hi]

theorem cleared_jacobian {k : ℕ} (P Q : Fin k → MvPolynomial (Fin k) ℝ)
    (x y : Fin k → ℝ) (hQ : ∀ i, MvPolynomial.eval x (Q i) ≠ 0)
    (hxy : rationalMap P Q x = y) :
    polynomialJacobian (cleared P Q y) x =
      Matrix.diagonal (fun i => MvPolynomial.eval x (Q i)) * rationalJacobian P Q x := by
  ext i j
  rw [Matrix.diagonal_mul]
  unfold polynomialJacobian cleared rationalJacobian rationalMap
  rw [rational_fderiv_single (P i) (Q i) x j (hQ i)]
  simp only [map_sub,MvPolynomial.pderiv_C_mul,map_mul,MvPolynomial.eval_C]
  have hi : y i = MvPolynomial.eval x (P i) / MvPolynomial.eval x (Q i) := (congrFun hxy i).symm
  rw [hi]
  field_simp [hQ i]
  <;> ring

theorem cleared_jacobian_det {k : ℕ} (P Q : Fin k → MvPolynomial (Fin k) ℝ)
    (x y : Fin k → ℝ) (hQ : ∀ i, MvPolynomial.eval x (Q i) ≠ 0)
    (hxy : rationalMap P Q x = y) :
    (polynomialJacobian (cleared P Q y) x).det =
      (∏ i, MvPolynomial.eval x (Q i)) * (rationalJacobian P Q x).det := by
  rw [cleared_jacobian P Q x y hQ hxy,Matrix.det_mul,Matrix.det_diagonal]

theorem cleared_jacobian_det_ne_zero {k : ℕ} (P Q : Fin k → MvPolynomial (Fin k) ℝ)
    (x y : Fin k → ℝ) (hQ : ∀ i, MvPolynomial.eval x (Q i) ≠ 0)
    (hxy : rationalMap P Q x = y) (hdet : (rationalJacobian P Q x).det ≠ 0) :
    (polynomialJacobian (cleared P Q y) x).det ≠ 0 := by
  rw [cleared_jacobian_det P Q x y hQ hxy]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hQ i)) hdet

end PaperI.RationalCount
