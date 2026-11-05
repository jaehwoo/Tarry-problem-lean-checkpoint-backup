import PaperILean.OriginalGaussPolynomialDegree

/-! The algebraic Jacobian in the cited nonsingular-zero theorem is the
actual analytic Jacobian of the manuscript's fixed-p,z polynomial pair.
-/
noncomputable section
namespace PaperI
open scoped BigOperators

def originalBivariateDifferential (P : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) • ContinuousLinearMap.proj i

theorem originalBivariateDifferential_apply (P : MvPolynomial (Fin 2) ℝ) (x v : Fin 2 → ℝ) :
    originalBivariateDifferential P x v=∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i P)*v i := by
  simp [originalBivariateDifferential,ContinuousLinearMap.sum_apply]

theorem originalBivariate_hasFDerivAt (P : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    HasFDerivAt (fun y => MvPolynomial.eval y P) (originalBivariateDifferential P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simpa [originalBivariateDifferential,MvPolynomial.pderiv_C] using (hasFDerivAt_const a x)
  | add P Q hP hQ =>
    have he : originalBivariateDifferential (P+Q) x=
        originalBivariateDifferential P x+originalBivariateDifferential Q x := by
      simp [originalBivariateDifferential,add_smul,Finset.sum_add_distrib]
    simpa [he] using hP.add hQ
  | mul_X P j hP =>
    have he : originalBivariateDifferential (P*MvPolynomial.X j) x=
        MvPolynomial.eval x P • ContinuousLinearMap.proj j+x j • originalBivariateDifferential P x := by
      ext v
      simp only [originalBivariateDifferential_apply,ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,
        MvPolynomial.pderiv_mul,map_add,map_mul,MvPolynomial.eval_X]
      simp [MvPolynomial.pderiv_X,Pi.single_apply,Finset.sum_add_distrib,
        Finset.mul_sum,mul_add,mul_assoc,mul_comm,mul_left_comm,add_comm]
    simpa [he] using hP.mul (hasFDerivAt_apply j x)

theorem originalBivariate_fderiv_single (P : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) (j : Fin 2) :
    fderiv ℝ (fun y => MvPolynomial.eval y P) x (Pi.single j 1)=
      MvPolynomial.eval x (MvPolynomial.pderiv j P) := by
  rw [(originalBivariate_hasFDerivAt P x).fderiv,originalBivariateDifferential_apply]
  simp [Pi.single_apply]

def originalBivariateJacobian (P Q : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![MvPolynomial.eval x (MvPolynomial.pderiv 0 P),MvPolynomial.eval x (MvPolynomial.pderiv 1 P);
     MvPolynomial.eval x (MvPolynomial.pderiv 0 Q),MvPolynomial.eval x (MvPolynomial.pderiv 1 Q)]

theorem originalBivariateJacobian_eq_fderiv (P Q : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    originalBivariateJacobian P Q x=
      !![fderiv ℝ (fun y => MvPolynomial.eval y P) x ![1,0],
         fderiv ℝ (fun y => MvPolynomial.eval y P) x ![0,1];
         fderiv ℝ (fun y => MvPolynomial.eval y Q) x ![1,0],
         fderiv ℝ (fun y => MvPolynomial.eval y Q) x ![0,1]] := by
  have hx : (Pi.single (0 : Fin 2) (1 : ℝ))=![1,0] := by ext i; fin_cases i <;> simp [Pi.single_apply]
  have hy : (Pi.single (1 : Fin 2) (1 : ℝ))=![0,1] := by ext i; fin_cases i <;> simp [Pi.single_apply]
  rw [← hx,← hy]
  simp only [originalBivariate_fderiv_single,originalBivariateJacobian]

theorem originalBivariateJacobian_transpose_det (P Q : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    (originalBivariateJacobian P Q x).transpose.det=(originalBivariateJacobian P Q x).det :=
  Matrix.det_transpose _

theorem originalGauss_polynomial_jacobian {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (p z : ℝ) (w : Fin 2 → ℝ) :
    originalBivariateJacobian
      (originalGaussPolynomialSlice (originalNormalPolynomial F n) z)
      (originalGaussPolynomialSlice (originalGaussSecondPolynomial F n p) z) w=
    originalGaussRootJacobian (originalGaussPhaseSlice (originalNormalPhase F n) z) p w := by
  let G := originalNormalPhase F n
  have hA : (fun u => MvPolynomial.eval u (originalGaussPolynomialSlice (originalNormalPolynomial F n) z))=
      originalGaussPhaseSlice G z := by
    funext u
    exact (originalGauss_polynomial_pair_eval F n p z u).1
  have hB : (fun u => MvPolynomial.eval u (originalGaussPolynomialSlice (originalGaussSecondPolynomial F n p) z))=
      (fun u => fderiv ℝ (originalGaussPhaseSlice G z) u ![p,1]) := by
    funext u
    have he := congrFun (originalGauss_phase_root_equations G z p u
      ((originalNormalPhase_contDiff F n 2).differentiable (by norm_num)).differentiableAt) 1
    change fderiv ℝ (originalGaussPhaseSlice G z) u ![p,1]=
      fderiv ℝ G ![u 0,u 1,z] ![0,1,0]+p*fderiv ℝ G ![u 0,u 1,z] ![1,0,0] at he
    exact (originalGauss_polynomial_pair_eval F n p z u).2.trans he.symm
  rw [originalBivariateJacobian_eq_fderiv,hA,hB]
  rfl

end PaperI
