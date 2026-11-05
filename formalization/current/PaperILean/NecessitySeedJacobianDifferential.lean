import PaperILean.AllDimAffinePullback
import PaperILean.NormalJacobianDifferential
import Mathlib.Tactic

open scoped BigOperators
noncomputable section
namespace PaperI.NecessitySeedJacobian

open PaperI.AllDim

private theorem monomialExponent_injective {k : ℕ} :
    Function.Injective (@AllDim.monomialExponent 3 k) := by
  intro a b h
  exact (AllDim.monomialIndexEquiv 3 k).injective (Subtype.ext h)

theorem coeff_coefficientPolynomial {k : ℕ} (F : AllDim.CoefficientSpace 3 k)
    (a : AllDim.MonomialIndex 3 k) :
    MvPolynomial.coeff (AllDim.monomialExponent a) (AllDim.coefficientPolynomial F) = F a := by
  classical
  rw [AllDim.coefficientPolynomial_eq_sum, MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial, monomialExponent_injective.eq_iff]

private theorem monomialExponent_ne_zero {k : ℕ} (a : AllDim.MonomialIndex 3 k) :
    AllDim.monomialExponent a ≠ 0 := by
  intro h
  have hs := AllDim.sum_monomialExponent a
  have hp := a.property.1
  simp [h] at hs
  omega

theorem coefficient_affineCoefficientMap {k : ℕ}
    (c : AllDim.PhysicalSpace 3) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (F : AllDim.CoefficientSpace 3 k) (a : AllDim.MonomialIndex 3 k) :
    (AllDim.affineCoefficientMap 3 k c B F) a =
      MvPolynomial.coeff (AllDim.monomialExponent a)
        (AllDim.affinePolynomialMap c B (AllDim.coefficientPolynomial F)) := by
  rw [← coeff_coefficientPolynomial (AllDim.affineCoefficientMap 3 k c B F) a,
    AllDim.polynomial_affineCoefficientMap,
    MvPolynomial.coeff_sub]
  simp [MvPolynomial.coeff_C, monomialExponent_ne_zero a,
    Ne.symm (monomialExponent_ne_zero a)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_coeff_affineCoordinate
    (c : E → AllDim.PhysicalSpace 3) (B : E → Fin 3 → Fin 3 → ℝ)
    (hc : ContDiff ℝ ⊤ c) (hB : ContDiff ℝ ⊤ B)
    (i : Fin 3) (e : Fin 3 →₀ ℕ) :
    ContDiff ℝ ⊤ (fun x => MvPolynomial.coeff e (AllDim.affineCoordinate (c x) (B x) i)) := by
  classical
  have hci := (contDiff_pi.mp hc) i
  have hBij (j : Fin 3) := (contDiff_pi.mp ((contDiff_pi.mp hB) i)) j
  simp only [AllDim.affineCoordinate, MvPolynomial.coeff_add, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C]
  apply ContDiff.add
  · split_ifs <;> fun_prop
  · apply ContDiff.sum
    intro j hj
    exact (hBij j).mul contDiff_const

theorem contDiff_coeff_affinePolynomialMap
    (c : E → AllDim.PhysicalSpace 3) (B : E → Fin 3 → Fin 3 → ℝ)
    (hc : ContDiff ℝ ⊤ c) (hB : ContDiff ℝ ⊤ B)
    (P : MvPolynomial (Fin 3) ℝ) :
    ∀ e : Fin 3 →₀ ℕ,
      ContDiff ℝ ⊤ (fun x => MvPolynomial.coeff e (AllDim.affinePolynomialMap (c x) (B x) P)) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r =>
      intro e
      simp only [AllDim.affinePolynomialMap, MvPolynomial.aeval_C]
      fun_prop
  | add P Q hP hQ =>
      intro e
      simp only [map_add, MvPolynomial.coeff_add]
      exact (hP e).add (hQ e)
  | mul_X P i hP =>
      intro e
      have hmul (x : E) :
          AllDim.affinePolynomialMap (c x) (B x) (P * MvPolynomial.X i) =
            AllDim.affinePolynomialMap (c x) (B x) P * AllDim.affineCoordinate (c x) (B x) i := by
        simp [AllDim.affinePolynomialMap]
      simp_rw [hmul, MvPolynomial.coeff_mul]
      apply ContDiff.sum
      intro d hd
      exact (hP d.1).mul (contDiff_coeff_affineCoordinate c B hc hB i d.2)

theorem contDiff_affineCoefficientMap_joint {k : ℕ}
    (c : E → AllDim.PhysicalSpace 3) (B : E → Fin 3 → Fin 3 → ℝ)
    (J : E → AllDim.CoefficientSpace 3 k)
    (hc : ContDiff ℝ ⊤ c) (hB : ContDiff ℝ ⊤ B) (hJ : ContDiff ℝ ⊤ J) :
    ContDiff ℝ ⊤ (fun x => AllDim.affineCoefficientMap 3 k (c x) (B x) (J x)) := by
  classical
  rw [contDiff_pi]
  intro a
  have hsum (x : E) :
      (AllDim.affineCoefficientMap 3 k (c x) (B x) (J x)) a =
        ∑ i : AllDim.MonomialIndex 3 k,
          J x i * (AllDim.affineCoefficientMap 3 k (c x) (B x) (Pi.single i (1 : ℝ) : AllDim.CoefficientSpace 3 k)) a := by
    have hJx : J x = ∑ i : AllDim.MonomialIndex 3 k, J x i • (Pi.single i (1 : ℝ) : AllDim.CoefficientSpace 3 k) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hJx, map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [hsum]
  apply ContDiff.sum
  intro i hi
  apply ((contDiff_pi.mp hJ) i).mul
  simp_rw [coefficient_affineCoefficientMap]
  exact contDiff_coeff_affinePolynomialMap c B hc hB
    (AllDim.coefficientPolynomial (Pi.single i (1 : ℝ) : AllDim.CoefficientSpace 3 k)) (AllDim.monomialExponent a)

def phaseEvaluation (k : ℕ) (x : AllDim.PhysicalSpace 3) :
    AllDim.CoefficientSpace 3 k →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun F => AllDim.phase F x
    map_add' := by
      intro F G
      simp [AllDim.phase, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro a F
      simp [AllDim.phase, smul_eq_mul, Finset.mul_sum, mul_assoc] }

@[simp] theorem phaseEvaluation_apply (k : ℕ) (x : AllDim.PhysicalSpace 3)
    (F : AllDim.CoefficientSpace 3 k) : phaseEvaluation k x F = AllDim.phase F x := rfl

theorem phase_eq_sum_eval {k : ℕ} (F : AllDim.CoefficientSpace 3 k)
    (x : AllDim.PhysicalSpace 3) :
    AllDim.phase F x = ∑ a : AllDim.MonomialIndex 3 k,
      F a * MvPolynomial.eval x (MvPolynomial.monomial (AllDim.monomialExponent a) (1 : ℝ)) := by
  classical
  rw [← AllDim.eval_coefficientPolynomial, AllDim.coefficientPolynomial_eq_sum,
    MvPolynomial.eval_sum]
  simp [MvPolynomial.eval_monomial, mul_comm]

theorem polynomialDifferential_coefficient_sum {k : ℕ}
    (F : AllDim.CoefficientSpace 3 k) (x : AllDim.PhysicalSpace 3) :
    PaperI.polynomialDifferential (AllDim.coefficientPolynomial F) x =
      ∑ a : AllDim.MonomialIndex 3 k,
        F a • PaperI.polynomialDifferential
          (MvPolynomial.monomial (AllDim.monomialExponent a) (1 : ℝ)) x := by
  classical
  have hs := HasFDerivAt.sum (x := x) (u := Finset.univ)
    (fun a _ => (PaperI.hasFDerivAt_evalPolynomial
      (MvPolynomial.monomial (AllDim.monomialExponent a) (1 : ℝ)) x).const_smul (F a))
  have heq : (fun y => ∑ a : AllDim.MonomialIndex 3 k,
      F a • MvPolynomial.eval y (MvPolynomial.monomial (AllDim.monomialExponent a) (1 : ℝ))) =
      (fun y => MvPolynomial.eval y (AllDim.coefficientPolynomial F)) := by
    funext y
    simpa only [smul_eq_mul, AllDim.eval_coefficientPolynomial] using (phase_eq_sum_eval F y).symm
  rw [heq] at hs
  exact (PaperI.hasFDerivAt_evalPolynomial (AllDim.coefficientPolynomial F) x).unique hs

theorem hasFDerivAt_phase_joint {k : ℕ}
    (J : E → AllDim.CoefficientSpace 3 k) (p : E → AllDim.PhysicalSpace 3)
    (dJ : E →L[ℝ] AllDim.CoefficientSpace 3 k) (dp : E →L[ℝ] AllDim.PhysicalSpace 3)
    (x : E) (hJ : HasFDerivAt J dJ x) (hp : HasFDerivAt p dp x) :
    HasFDerivAt (fun y => AllDim.phase (J y) (p y))
      ((phaseEvaluation k (p x)).comp dJ +
        (PaperI.polynomialDifferential (AllDim.coefficientPolynomial (J x)) (p x)).comp dp) x := by
  classical
  have hs := HasFDerivAt.sum (x := x) (u := Finset.univ)
    (fun a _ =>
      (((ContinuousLinearMap.proj a : AllDim.CoefficientSpace 3 k →L[ℝ] ℝ).hasFDerivAt).comp x hJ).mul
        ((PaperI.hasFDerivAt_evalPolynomial
          (MvPolynomial.monomial (AllDim.monomialExponent a) (1 : ℝ)) (p x)).comp x hp))
  convert hs using 1
  · funext y
    exact phase_eq_sum_eval (J y) (p y)
  · ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      phaseEvaluation_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, Function.comp_apply]
    rw [phase_eq_sum_eval, polynomialDifferential_coefficient_sum]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, add_comm]
    apply congrArg₂ (fun a b : ℝ => a + b)
    · rfl
    · apply Finset.sum_congr rfl
      intro a ha
      ring

def matrixApplication (z : AllDim.PhysicalSpace 3) :
    (Fin 3 → Fin 3 → ℝ) →L[ℝ] AllDim.PhysicalSpace 3 :=
  LinearMap.toContinuousLinearMap {
    toFun := fun B i => ∑ j, B i j * z j
    map_add' := by
      intro A B
      ext i
      simp [add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro a B
      ext i
      simp [smul_eq_mul, Finset.mul_sum, mul_assoc] }

@[simp] theorem matrixApplication_apply (z : AllDim.PhysicalSpace 3)
    (B : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    matrixApplication z B i = ∑ j, B i j * z j := rfl

theorem hasFDerivAt_affinePoint
    (c : E → AllDim.PhysicalSpace 3) (B : E → Fin 3 → Fin 3 → ℝ)
    (dc : E →L[ℝ] AllDim.PhysicalSpace 3)
    (dB : E →L[ℝ] (Fin 3 → Fin 3 → ℝ)) (x : E)
    (hc : HasFDerivAt c dc x) (hB : HasFDerivAt B dB x)
    (z : AllDim.PhysicalSpace 3) :
    HasFDerivAt (fun y => AllDim.affinePoint (c y) (B y) z)
      (dc + (matrixApplication z).comp dB) x := by
  exact hc.add ((matrixApplication z).hasFDerivAt.comp x hB)

theorem fderiv_affineCoefficientMap_phase {k : ℕ}
    (c : E → AllDim.PhysicalSpace 3) (B : E → Fin 3 → Fin 3 → ℝ)
    (J : E → AllDim.CoefficientSpace 3 k)
    (hc : ContDiff ℝ ⊤ c) (hB : ContDiff ℝ ⊤ B) (hJ : ContDiff ℝ ⊤ J)
    (x v : E) (z : AllDim.PhysicalSpace 3) :
    AllDim.phase
        (fderiv ℝ (fun y => AllDim.affineCoefficientMap 3 k (c y) (B y) (J y)) x v) z =
      AllDim.phase (fderiv ℝ J x v) (AllDim.affinePoint (c x) (B x) z) -
        AllDim.phase (fderiv ℝ J x v) (c x) +
      PaperI.polynomialDifferential (AllDim.coefficientPolynomial (J x))
        (AllDim.affinePoint (c x) (B x) z)
        (fderiv ℝ c x v + matrixApplication z (fderiv ℝ B x v)) -
      PaperI.polynomialDifferential (AllDim.coefficientPolynomial (J x)) (c x)
        (fderiv ℝ c x v) := by
  have hc' := (hc.differentiable (by simp)).differentiableAt.hasFDerivAt (x := x)
  have hB' := (hB.differentiable (by simp)).differentiableAt.hasFDerivAt (x := x)
  have hJ' := (hJ.differentiable (by simp)).differentiableAt.hasFDerivAt (x := x)
  have hG := ((contDiff_affineCoefficientMap_joint c B J hc hB hJ).differentiable
    (by simp)).differentiableAt.hasFDerivAt (x := x)
  have hEval := (phaseEvaluation k z).hasFDerivAt.comp x hG
  have hp := hasFDerivAt_affinePoint c B _ _ x hc' hB' z
  have hs := hasFDerivAt_phase_joint J (fun y => AllDim.affinePoint (c y) (B y) z)
    _ _ x hJ' hp
  have ht := hasFDerivAt_phase_joint J c _ _ x hJ' hc'
  have hScalar := hs.sub ht
  have hScalar' : HasFDerivAt
      (fun y => AllDim.phase (AllDim.affineCoefficientMap 3 k (c y) (B y) (J y)) z)
      (((phaseEvaluation k (AllDim.affinePoint (c x) (B x) z)).comp (fderiv ℝ J x) +
          (PaperI.polynomialDifferential (AllDim.coefficientPolynomial (J x))
            (AllDim.affinePoint (c x) (B x) z)).comp
            (fderiv ℝ c x + (matrixApplication z).comp (fderiv ℝ B x))) -
        ((phaseEvaluation k (c x)).comp (fderiv ℝ J x) +
          (PaperI.polynomialDifferential (AllDim.coefficientPolynomial (J x))
            (c x)).comp (fderiv ℝ c x))) x := by
    simpa only [AllDim.phase_affineCoefficientMap] using hScalar
  have h := congrArg (fun L : E →L[ℝ] ℝ => L v) (hEval.unique hScalar')
  simp only [ContinuousLinearMap.comp_apply, phaseEvaluation_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply] at h
  linarith

end PaperI.NecessitySeedJacobian
