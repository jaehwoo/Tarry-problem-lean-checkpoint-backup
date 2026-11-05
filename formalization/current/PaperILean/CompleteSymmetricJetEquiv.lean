import PaperILean.SymmetricTensorPolynomial
import PaperILean.CompleteJetTaylorTransport
import Mathlib.Algebra.MvPolynomial.Funext

/-! The whole nonconstant coefficient space and all symmetric positive jets.
The inverse is the finite diagonal Taylor polynomial with the source factorials.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

abbrev CompleteSymmetricJets (k : ℕ) := (r : Fin k) → SymmetricTensor (r.val + 1)

theorem phase_add_eq {k : ℕ} (F G : CoefficientSpace k) :
    phase (F + G) = phase F + phase G := by
  funext x
  simp [phase, add_mul, Finset.sum_add_distrib]

theorem phase_smul_eq {k : ℕ} (a : ℝ) (F : CoefficientSpace k) :
    phase (a • F) = a • phase F := by
  funext x
  simp [phase, mul_assoc, Finset.mul_sum]

theorem phase_injective (k : ℕ) : Function.Injective (@phase k) := by
  intro F G h
  apply (coefficientPolynomialEquiv k).injective
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.eval x (coefficientPolynomial F) =
    MvPolynomial.eval x (coefficientPolynomial G)
  simpa only [eval_coefficientPolynomial] using congrFun h x

def completeJetSymmetricMap (k : ℕ) : CoefficientSpace k →ₗ[ℝ] CompleteSymmetricJets k where
  toFun F r := ⟨iteratedFDeriv ℝ (r.val + 1) (phase F) 0,
    iteratedFDeriv_phase_perm F (r.val + 1) 0⟩
  map_add' F G := by
    funext r
    apply Subtype.ext
    change iteratedFDeriv ℝ (r.val + 1) (phase (F + G)) 0 =
      iteratedFDeriv ℝ (r.val + 1) (phase F) 0 + iteratedFDeriv ℝ (r.val + 1) (phase G) 0
    rw [phase_add_eq]
    exact iteratedFDeriv_add_apply (contDiff_phase F _).contDiffAt
      (contDiff_phase G _).contDiffAt
  map_smul' a F := by
    funext r
    apply Subtype.ext
    change iteratedFDeriv ℝ (r.val + 1) (phase (a • F)) 0 =
      a • iteratedFDeriv ℝ (r.val + 1) (phase F) 0
    rw [phase_smul_eq]
    exact iteratedFDeriv_const_smul_apply (contDiff_phase F _).contDiffAt

def symmetricJetPolynomial {k : ℕ} (T : CompleteSymmetricJets k) : MvPolynomial (Fin 3) ℝ :=
  ∑ r : Fin k, (((r.val + 1).factorial : ℝ)⁻¹) • tensorDiagonalPolynomial (T r).val

theorem symmetricJetPolynomial_totalDegree {k : ℕ} (T : CompleteSymmetricJets k) :
    (symmetricJetPolynomial T).totalDegree ≤ k := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r _
  exact (MvPolynomial.totalDegree_smul_le _ _).trans
    ((totalDegree_tensorDiagonalPolynomial_le _).trans (Nat.succ_le_of_lt r.isLt))

theorem tensorDiagonalPolynomial_zero {n : ℕ} (T : TensorSpace (n + 1)) :
    MvPolynomial.coeff 0 (tensorDiagonalPolynomial T) = 0 := by
  change MvPolynomial.constantCoeff (tensorDiagonalPolynomial T) = 0
  rw [← MvPolynomial.eval_zero, eval_tensorDiagonalPolynomial]
  exact T.map_coord_zero (0 : Fin (n + 1)) rfl

theorem symmetricJetPolynomial_constantCoeff {k : ℕ} (T : CompleteSymmetricJets k) :
    MvPolynomial.coeff 0 (symmetricJetPolynomial T) = 0 := by
  classical
  simp [symmetricJetPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    tensorDiagonalPolynomial_zero]

theorem symmetricJetPolynomial_mem {k : ℕ} (T : CompleteSymmetricJets k) :
    symmetricJetPolynomial T ∈ zeroConstantPolynomialSpace k :=
  (mem_zeroConstantPolynomialSpace k _).mpr
    ⟨symmetricJetPolynomial_totalDegree T, symmetricJetPolynomial_constantCoeff T⟩

theorem symmetricJetPolynomial_add {k : ℕ} (T S : CompleteSymmetricJets k) :
    symmetricJetPolynomial (T + S) = symmetricJetPolynomial T + symmetricJetPolynomial S := by
  classical
  simp [symmetricJetPolynomial, tensorDiagonalPolynomial_add, smul_add,
    Finset.sum_add_distrib]

theorem symmetricJetPolynomial_smul {k : ℕ} (a : ℝ) (T : CompleteSymmetricJets k) :
    symmetricJetPolynomial (a • T) = a • symmetricJetPolynomial T := by
  classical
  simp [symmetricJetPolynomial, tensorDiagonalPolynomial_smul, Finset.smul_sum,
    smul_smul, mul_comm]

def symmetricJetCoefficientMap (k : ℕ) : CompleteSymmetricJets k →ₗ[ℝ] CoefficientSpace k := by
  let L : CompleteSymmetricJets k →ₗ[ℝ] zeroConstantPolynomialSpace k :=
    { toFun := fun T => ⟨symmetricJetPolynomial T, symmetricJetPolynomial_mem T⟩
      map_add' := fun T S => Subtype.ext (symmetricJetPolynomial_add T S)
      map_smul' := fun a T => Subtype.ext (symmetricJetPolynomial_smul a T) }
  exact (coefficientPolynomialEquiv k).symm.toLinearMap.comp L

theorem coefficientPolynomial_symmetricJetCoefficientMap {k : ℕ} (T : CompleteSymmetricJets k) :
    coefficientPolynomial (symmetricJetCoefficientMap k T) = symmetricJetPolynomial T := by
  change ((coefficientPolynomialEquiv k)
    ((coefficientPolynomialEquiv k).symm ⟨_, symmetricJetPolynomial_mem T⟩)).val = _
  rw [LinearEquiv.apply_symm_apply]

theorem phase_symmetricJetCoefficientMap {k : ℕ} (T : CompleteSymmetricJets k) :
    phase (symmetricJetCoefficientMap k T) = fun x =>
      ∑ r : Fin k, (((r.val + 1).factorial : ℝ)⁻¹) * (T r).val (fun _ => x) := by
  funext x
  rw [← eval_coefficientPolynomial, coefficientPolynomial_symmetricJetCoefficientMap]
  simp [symmetricJetPolynomial, MvPolynomial.smul_eq_C_mul,
    eval_tensorDiagonalPolynomial, smul_eq_mul]

theorem symmetricJetCoefficientMap_left_inverse (k : ℕ) (F : CoefficientSpace k) :
    symmetricJetCoefficientMap k (completeJetSymmetricMap k F) = F := by
  apply phase_injective k
  funext x
  rw [phase_symmetricJetCoefficientMap]
  have ht := phase_finite_taylor F 0 x
  simp only [zero_add, phase_zero, sub_zero] at ht
  rw [ht]
  dsimp only [completeJetSymmetricMap, LinearMap.coe_mk, AddHom.coe_mk]
  exact Fin.sum_univ_eq_sum_range (fun n => ((n + 1).factorial : ℝ)⁻¹ *
    iteratedFDeriv ℝ (n + 1) (phase F) 0 (fun _ => x)) k

theorem symmetricJetCoefficientMap_right_inverse (k : ℕ) (T : CompleteSymmetricJets k) :
    completeJetSymmetricMap k (symmetricJetCoefficientMap k T) = T := by
  classical
  funext r
  apply Subtype.ext
  apply ContinuousMultilinearMap.ext
  intro v
  change iteratedFDeriv ℝ (r.val + 1) (phase (symmetricJetCoefficientMap k T)) 0 v = _
  rw [phase_symmetricJetCoefficientMap]
  have hs : ∀ j : Fin k, ContDiff ℝ ((r.val + 1 : ℕ) : WithTop ℕ∞)
      (fun x : PhysicalSpace => (((j.val + 1).factorial : ℝ)⁻¹) *
        (T j).val (fun _ => x)) := by
    intro j
    exact contDiff_const.mul ((T j).val.contDiff.comp (contDiff_pi.mpr (fun _ => contDiff_id)))
  have hsum := iteratedFDeriv_sum (i := r.val + 1) (fun j (_ : j ∈ Finset.univ) => hs j)
  rw [hsum]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
  rw [Finset.sum_eq_single r]
  · rw [show (fun x : PhysicalSpace => (((r.val + 1).factorial : ℝ)⁻¹) *
      (T r).val (fun _ => x)) = (((r.val + 1).factorial : ℝ)⁻¹) •
      (fun x : PhysicalSpace => (T r).val (fun _ => x)) by rfl]
    have hc : ContDiffAt ℝ ((r.val + 1 : ℕ) : WithTop ℕ∞)
        (fun x : PhysicalSpace => (T r).val (fun _ => x)) 0 :=
      ((T r).val.contDiff.comp (contDiff_pi.mpr (fun _ => contDiff_id))).contDiffAt
    rw [iteratedFDeriv_const_smul_apply hc]
    rw [ContinuousMultilinearMap.smul_apply, symmetricTensor_diagonal_derivative]
    simp [smul_eq_mul, ← mul_assoc, Nat.factorial_ne_zero]
  · intro j _ hj
    rw [show (fun x : PhysicalSpace => (((j.val + 1).factorial : ℝ)⁻¹) *
      (T j).val (fun _ => x)) = (((j.val + 1).factorial : ℝ)⁻¹) •
      (fun x : PhysicalSpace => (T j).val (fun _ => x)) by rfl]
    have hc : ContDiffAt ℝ ((r.val + 1 : ℕ) : WithTop ℕ∞)
        (fun x : PhysicalSpace => (T j).val (fun _ => x)) 0 :=
      ((T j).val.contDiff.comp (contDiff_pi.mpr (fun _ => contDiff_id))).contDiffAt
    rw [iteratedFDeriv_const_smul_apply hc]
    rw [ContinuousMultilinearMap.smul_apply, tensor_diagonal_derivative_other]
    · simp
    · intro h
      apply hj
      apply Fin.ext
      omega
  · simp

def completeJetSymmetricEquiv (k : ℕ) : CoefficientSpace k ≃ₗ[ℝ] CompleteSymmetricJets k where
  toLinearMap := completeJetSymmetricMap k
  invFun := symmetricJetCoefficientMap k
  left_inv := symmetricJetCoefficientMap_left_inverse k
  right_inv := symmetricJetCoefficientMap_right_inverse k

def affineCompleteJetSymmetricEquiv (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) :
    CoefficientSpace k ≃ₗ[ℝ] CompleteSymmetricJets k :=
  (affineCoefficientEquiv k c B hB).trans (completeJetSymmetricEquiv k)

theorem affineCompleteJetSymmetricEquiv_apply (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) (F : CoefficientSpace k)
    (r : Fin k) (v : Fin (r.val + 1) → PhysicalSpace) :
    (affineCompleteJetSymmetricEquiv k c B hB F r).val v =
      iteratedFDeriv ℝ (r.val + 1) (phase F) c (fun j => B *ᵥ v j) := by
  change iteratedFDeriv ℝ (r.val + 1) (phase (affineCoefficientMap k c B F)) 0 v = _
  exact iteratedFDeriv_phase_affine_zero_positive k c B F r.val v

end PaperI
