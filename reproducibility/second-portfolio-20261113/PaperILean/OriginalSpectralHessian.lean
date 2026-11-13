import PaperILean.SymmetricCongruence
import PaperILean.LogEnergyGradient
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The exact log-square specialization of the spectral Hessian used at I222.
The Hessian is the genuine iterated Fréchet derivative. Its calculation uses
only the already checked first differential, and does not use the existing
second derivative of the source curve. Collision cases are retained. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology Matrix Matrix.L2OpNorm
namespace PaperI

set_option maxHeartbeats 800000

def originalLogDifferential {n : ℕ} (A V : SymmetricMatrix n) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((symmetricMatrixExpDifferentialEquiv (symmetricMatrixLog A)).symm V :
    Matrix (Fin n) (Fin n) ℝ)

def originalLogEnergyHessian {n : ℕ} (A : SymmetricMatrix n) :
    SymmetricMatrix n →L[ℝ] SymmetricMatrix n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ symmetricLogEnergy) A

theorem original_logEnergy_fderiv_trace {n : ℕ} (A V : SymmetricMatrix n)
    (hA : A.val.PosDef) :
    fderiv ℝ symmetricLogEnergy A V =
      2 * Matrix.trace (CFC.log A.val * A.val⁻¹ * V.val) := by
  rw [(symmetricLogEnergy_posDef_hasFDerivAt A hA).fderiv]
  exact symmetricLogEnergyDifferential_eq_trace_inverse A V hA

theorem original_hasDerivAt_matrix_inverse {n : ℕ}
    {B : ℝ → Matrix (Fin n) (Fin n) ℝ} {V : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hB : HasDerivAt B V t) (hu : IsUnit (B t)) :
    HasDerivAt (fun s => (B s)⁻¹) (-(B t)⁻¹ * V * (B t)⁻¹) t := by
  obtain ⟨U, hU⟩ := hu
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) U
  rw [hU] at hi
  have hd := hi.comp_hasDerivAt t hB
  simpa only [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    Matrix.coe_units_inv, hU, neg_mul] using hd

theorem original_logEnergy_hessian_trace {n : ℕ} (A V W : SymmetricMatrix n)
    (hA : A.val.PosDef) :
    originalLogEnergyHessian A V W =
      2 * Matrix.trace (originalLogDifferential A V * A.val⁻¹ * W.val -
        CFC.log A.val * A.val⁻¹ * V.val * A.val⁻¹ * W.val) := by
  let γ : ℝ → SymmetricMatrix n := fun t => A + t • V
  have hγ : HasDerivAt γ V 0 := by
    simpa only [γ, zero_smul, add_zero, id_eq, one_smul, zero_add] using
      (hasDerivAt_const (0 : ℝ) A).add ((hasDerivAt_id (0 : ℝ)).smul_const V)
  have hγ0 : γ 0 = A := by simp [γ]
  have hmat : HasDerivAt (fun t => (γ t).val) V.val 0 := by
    simpa only [Function.comp_def] using
      (symmetricMatrixIncl n).hasFDerivAt.comp_hasDerivAt 0 hγ
  have hlog : HasDerivAt (fun t => CFC.log (γ t).val)
      (originalLogDifferential A V) 0 := by
    have hl := (symmetricMatrixLog_posDef_hasFDerivAt A hA).comp_hasDerivAt_of_eq 0
      hγ hγ0.symm
    have hi := (symmetricMatrixIncl n).hasFDerivAt.comp_hasDerivAt 0 hl
    simpa only [Function.comp_def, originalLogDifferential, symmetricMatrixLog,
      symmetricMatrixOf, symmetricMatrixIncl, Submodule.subtypeL_apply] using hi
  have hinv : HasDerivAt (fun t => (γ t).val⁻¹) (-A.val⁻¹ * V.val * A.val⁻¹) 0 := by
    simpa only [hγ0] using original_hasDerivAt_matrix_inverse hmat (by simpa only [hγ0] using hA.isUnit)
  have hp := ((hlog.mul hinv).mul_const W.val)
  have ht := ((matrixTraceCLM n).hasFDerivAt.comp_hasDerivAt 0 hp).const_mul 2
  have heq : (fun t => fderiv ℝ symmetricLogEnergy (γ t) W) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => 2 * Matrix.trace (CFC.log (γ t).val * (γ t).val⁻¹ * W.val)) := by
    have hc : ∀ᶠ t in 𝓝 (0 : ℝ), (γ t).val.PosDef :=
      hγ.continuousAt.preimage_mem_nhds
        ((isOpen_positiveSymmetricCone n).mem_nhds (by simpa only [hγ0] using hA))
    filter_upwards [hc] with t ht
    exact original_logEnergy_fderiv_trace (γ t) W ht
  have hgrad := ((contDiffAt_symmetricLogEnergy A hA).fderiv_right
    (m := ⊤) (by simp)).differentiableAt (by simp)
  have hg := (hgrad.hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ hγ0.symm).clm_apply
    (hasDerivAt_const (0 : ℝ) W)
  have hd := ht.congr_of_eventuallyEq heq
  have hu := hg.unique hd
  simp only [hγ0, zero_smul, ContinuousLinearMap.map_zero, add_zero,
    matrixTraceCLM_apply, Function.comp_def] at hu
  change originalLogEnergyHessian A V W = _ at hu
  rw [hu]
  congr 2
  noncomm_ring


theorem original_exponentialDiagonal_inverse {n : ℕ} (a : Fin n → ℝ) :
    (exponentialDiagonal a)⁻¹ = Matrix.diagonal (fun i => (Real.exp (a i))⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [exponentialDiagonal, Matrix.diagonal_mul_diagonal]
  simp only [inv_mul_cancel₀ (Real.exp_ne_zero _), Matrix.diagonal_one]

theorem originalLogDifferential_diagonal {n : ℕ} (a : Fin n → ℝ)
    (V : SymmetricMatrix n) (i j : Fin n) :
    originalLogDifferential (symmetricMatrixDiagonal (fun i => Real.exp (a i))) V i j =
      (expDividedDifference (a i) (a j))⁻¹ * V.val i j := by
  have he := (symmetricMatrixLog_posDef_hasFDerivAt
    (symmetricMatrixDiagonal (fun i => Real.exp (a i))) (exponentialDiagonal_posDef a)).unique
      (symmetricMatrixLog_diagonal_hasStrictFDerivAt a).hasFDerivAt
  have hv := congrArg (fun L : SymmetricMatrix n →L[ℝ] SymmetricMatrix n =>
    ((L V : SymmetricMatrix n) : Matrix (Fin n) (Fin n) ℝ) i j) he
  change originalLogDifferential (symmetricMatrixDiagonal (fun i => Real.exp (a i))) V i j =
    (diagonalExpDifferentialEquiv a).symm V.val i j at hv
  rw [hv, diagonalExpDifferentialEquiv_symm_apply]

def originalSpectralEntryCoefficient (a b : ℝ) : ℝ :=
  2 * ((expDividedDifference a b)⁻¹ / Real.exp b - a / Real.exp a / Real.exp b)

theorem originalSpectralEntryCoefficient_self (a : ℝ) :
    originalSpectralEntryCoefficient a a = logSquareSecond (Real.exp a) := by
  simp only [originalSpectralEntryCoefficient, expDividedDifference_self,
    logSquareSecond, Real.log_exp]
  field_simp [Real.exp_ne_zero] <;> ring_nf <;> simp

theorem originalSpectralEntryCoefficient_pair (a b : ℝ) :
    originalSpectralEntryCoefficient a b + originalSpectralEntryCoefficient b a =
      2 * logSquareDividedDifference (Real.exp a) (Real.exp b) := by
  by_cases hab : a = b
  · subst b
    rw [originalSpectralEntryCoefficient_self, logSquareDividedDifference_self]
    ring
  · have he : Real.exp a ≠ Real.exp b := fun h => hab (Real.exp_injective h)
    simp only [originalSpectralEntryCoefficient, expDividedDifference, hab, Ne.symm hab,
      if_false, logSquareDividedDifference, he, logSquareFirst, Real.log_exp]
    field_simp [Real.exp_ne_zero a, Real.exp_ne_zero b, sub_ne_zero.mpr hab,
      sub_ne_zero.mpr (Ne.symm hab), sub_ne_zero.mpr he, sub_ne_zero.mpr (Ne.symm he)]
    ring

theorem original_matrix_ordered_pair_sum {n : ℕ} (w : Fin n → Fin n → ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (hV : V.IsSymm) :
    (∑ i, ∑ j, w i j * (V i j)^2) = (∑ i, w i i * (V i i)^2) +
      ∑ i, ∑ j, if i < j then (w i j + w j i) * (V i j)^2 else 0 := by
  have hgt : (∑ i, ∑ j, if j < i then w i j * (V i j)^2 else 0) =
      ∑ i, ∑ j, if i < j then w j i * (V i j)^2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hV.apply i j]
  have htri (i j : Fin n) : w i j * (V i j)^2 =
      (if i = j then w i j * (V i j)^2 else 0) +
      (if i < j then w i j * (V i j)^2 else 0) +
      (if j < i then w i j * (V i j)^2 else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, ne_of_lt hij, not_lt_of_ge hij.le]
    · subst j; simp
    · simp [hij, (ne_of_lt hij).symm, not_lt_of_ge hij.le]
  calc
    _ = ∑ i, ∑ j, ((if i = j then w i j * (V i j)^2 else 0) +
        (if i < j then w i j * (V i j)^2 else 0) +
        (if j < i then w i j * (V i j)^2 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun j _ => htri i j)
    _ = (∑ i, w i i * (V i i)^2) +
        (∑ i, ∑ j, if i < j then w i j * (V i j)^2 else 0) +
        (∑ i, ∑ j, if j < i then w i j * (V i j)^2 else 0) := by
      simp [Finset.sum_add_distrib]
    _ = _ := by
      rw [hgt, add_assoc, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i < j <;> simp only [hij, if_true, if_false] <;> ring

theorem original_logEnergy_hessian_diagonal_ordered {n : ℕ} (a : Fin n → ℝ)
    (V : SymmetricMatrix n) :
    originalLogEnergyHessian (symmetricMatrixDiagonal (fun i => Real.exp (a i))) V V =
      ∑ i, ∑ j, originalSpectralEntryCoefficient (a i) (a j) * (V.val i j)^2 := by
  rw [original_logEnergy_hessian_trace _ _ _ (exponentialDiagonal_posDef a)]
  change 2 * Matrix.trace
    (originalLogDifferential (symmetricMatrixDiagonal (fun i => Real.exp (a i))) V *
      (exponentialDiagonal a)⁻¹ * V.val -
      CFC.log (exponentialDiagonal a) * (exponentialDiagonal a)⁻¹ * V.val *
        (exponentialDiagonal a)⁻¹ * V.val) = _
  rw [original_exponentialDiagonal_inverse, sourceMatrix_log_exponentialDiagonal]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.sub_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.diagonal_mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, originalLogDifferential_diagonal]
  rw [V.property.apply i j]
  unfold originalSpectralEntryCoefficient
  simp only [div_eq_mul_inv]
  ring

theorem original_logEnergy_hessian_diagonal {n : ℕ} (a : Fin n → ℝ)
    (V : SymmetricMatrix n) :
    originalLogEnergyHessian (symmetricMatrixDiagonal (fun i => Real.exp (a i))) V V =
      diagonalLogSpectralHessian a V.val := by
  rw [original_logEnergy_hessian_diagonal_ordered,
    original_matrix_ordered_pair_sum _ V.val V.property]
  unfold diagonalLogSpectralHessian
  simp only [originalSpectralEntryCoefficient_self, originalSpectralEntryCoefficient_pair]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j <;> simp only [hij, if_true, if_false, mul_zero] <;> ring


theorem original_logEnergy_line_second {n : ℕ} (A V : SymmetricMatrix n)
    (hA : A.val.PosDef) :
    HasDerivAt (deriv (fun t : ℝ => symmetricLogEnergy (A + t • V)))
      (originalLogEnergyHessian A V V) 0 := by
  have hline (t : ℝ) : HasDerivAt (fun u : ℝ => A + u • V) V t := by
    simpa using (hasDerivAt_const t A).add ((hasDerivAt_id t).smul_const V)
  have hc : ∀ᶠ t in 𝓝 (0 : ℝ), (A + t • V).val.PosDef := by
    have h := (hline 0).continuousAt.preimage_mem_nhds
      ((isOpen_positiveSymmetricCone n).mem_nhds (by simpa using hA))
    exact h
  have heq : deriv (fun t : ℝ => symmetricLogEnergy (A + t • V)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => fderiv ℝ symmetricLogEnergy (A + t • V) V) := by
    filter_upwards [hc] with t ht
    exact ((symmetricLogEnergy_posDef_hasFDerivAt (A + t • V) ht).differentiableAt.hasFDerivAt.comp_hasDerivAt
      t (hline t)).deriv
  have hgrad := ((contDiffAt_symmetricLogEnergy A hA).fderiv_right
    (m := ⊤) (by simp)).differentiableAt (by simp)
  have hg := (hgrad.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hline 0) (by simp)).clm_apply
    (hasDerivAt_const (0 : ℝ) V)
  have hd := hg.congr_of_eventuallyEq heq
  simpa only [zero_smul, add_zero, map_zero, originalLogEnergyHessian] using hd

theorem original_logEnergy_hessian_conjugate {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ)) (A V : SymmetricMatrix n)
    (hA : A.val.PosDef) :
    originalLogEnergyHessian (symmetricOrthogonalConjugateEquiv U A)
      (symmetricOrthogonalConjugateEquiv U V) (symmetricOrthogonalConjugateEquiv U V) =
      originalLogEnergyHessian A V V := by
  let L := symmetricOrthogonalConjugateEquiv U
  have hline : HasDerivAt (fun t : ℝ => A + t • V) V 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) A).add
      ((hasDerivAt_id (0 : ℝ)).smul_const V)
  have hc : ∀ᶠ t in 𝓝 (0 : ℝ), (A + t • V).val.PosDef :=
    hline.continuousAt.preimage_mem_nhds
      ((isOpen_positiveSymmetricCone n).mem_nhds (by simpa using hA))
  have heq : (fun t : ℝ => symmetricLogEnergy (L A + t • L V)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => symmetricLogEnergy (A + t • V)) := by
    filter_upwards [hc] with t ht
    rw [← L.map_smul, ← L.map_add]
    exact sourceMatrixLogEnergy_orthogonalConjugate U (A + t • V).val ht
  have hd := original_logEnergy_line_second (L A) (L V)
    (orthogonalConjugate_posDef U A.val hA)
  exact hd.unique ((original_logEnergy_line_second A V hA).congr_of_eventuallyEq heq.deriv)

theorem original_logEnergy_hessian_spectral {n : ℕ} (A V : SymmetricMatrix n)
    (hA : A.val.PosDef) :
    originalLogEnergyHessian A V V =
      diagonalLogSpectralHessian (fun i => Real.log (hA.isHermitian.eigenvalues i))
        (orthogonalConjugate (star hA.isHermitian.eigenvectorUnitary) V.val) := by
  let a : Fin n → ℝ := fun i => Real.log (hA.isHermitian.eigenvalues i)
  let U := star hA.isHermitian.eigenvectorUnitary
  have he : symmetricOrthogonalConjugateEquiv U A =
      symmetricMatrixDiagonal (fun i => Real.exp (a i)) := by
    apply Subtype.ext
    change orthogonalConjugate U A.val = Matrix.diagonal (fun i => Real.exp (a i))
    rw [sourceMatrix_eigenbasis_diagonal A.val hA]
    apply congrArg Matrix.diagonal
    funext i
    exact (Real.exp_log (hA.eigenvalues_pos i)).symm
  rw [← original_logEnergy_hessian_conjugate U A V hA, he]
  exact original_logEnergy_hessian_diagonal a (symmetricOrthogonalConjugateEquiv U V)


theorem original_logEnergy_fderiv_diagonal {n : ℕ} (a : Fin n → ℝ)
    (W : SymmetricMatrix n) :
    fderiv ℝ symmetricLogEnergy (symmetricMatrixDiagonal (fun i => Real.exp (a i))) W =
      diagonalLogSpectralGradient a W.val := by
  rw [original_logEnergy_fderiv_trace _ _ (exponentialDiagonal_posDef a)]
  change 2 * Matrix.trace (CFC.log (exponentialDiagonal a) *
    (exponentialDiagonal a)⁻¹ * W.val) = _
  rw [sourceMatrix_log_exponentialDiagonal, original_exponentialDiagonal_inverse]
  simp only [Matrix.diagonal_mul_diagonal, Matrix.trace, Matrix.diag_apply,
    Matrix.diagonal_mul, Finset.mul_sum, diagonalLogSpectralGradient,
    logSquareFirst, Real.log_exp, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem original_logEnergy_second_chain_rule {n : ℕ}
    (γ : ℝ → SymmetricMatrix n) (W : SymmetricMatrix n)
    (hp : ∀ t, (γ t).val.PosDef) (hγ : ∀ t, DifferentiableAt ℝ γ t)
    (hγ2 : HasDerivAt (deriv γ) W 0) :
    HasDerivAt (deriv (fun t => symmetricLogEnergy (γ t)))
      (originalLogEnergyHessian (γ 0) (deriv γ 0) (deriv γ 0) +
        fderiv ℝ symmetricLogEnergy (γ 0) W) 0 := by
  have heq : deriv (fun t => symmetricLogEnergy (γ t)) =
      fun t => fderiv ℝ symmetricLogEnergy (γ t) (deriv γ t) := by
    funext t
    exact ((symmetricLogEnergy_posDef_hasFDerivAt (γ t) (hp t)).differentiableAt.hasFDerivAt.comp_hasDerivAt
      t (hγ t).hasDerivAt).deriv
  have hgrad := ((contDiffAt_symmetricLogEnergy (γ 0) (hp 0)).fderiv_right
    (m := ⊤) (by simp)).differentiableAt (by simp)
  have hd := (hgrad.hasFDerivAt.comp_hasDerivAt 0 (hγ 0).hasDerivAt).clm_apply hγ2
  rw [heq]
  exact hd

theorem original_symmetricSourceCurve_hasDerivAt {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    HasDerivAt (symmetricSourceCurve A hA H hH)
      ((symmetricMatrixProjection n) (deriv (sourceMatrixCurve A hA H) t)) t := by
  have hc := (hasDerivAt_sourceMatrixCurve A hA H t).differentiableAt.hasDerivAt
  have hp := (symmetricMatrixProjection n).hasFDerivAt.comp_hasDerivAt t hc
  have he : (symmetricMatrixProjection n) ∘ sourceMatrixCurve A hA H =
      symmetricSourceCurve A hA H hH := by
    funext u
    exact symmetricMatrixProjection_of_symm _
      ((realMatrix_isHermitian_iff_isSymm _).mp
        (sourceMatrixCurve_posDef A hA H hH u).isHermitian)
  rw [he] at hp
  exact hp

theorem original_symmetricSourceCurve_deriv {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    deriv (symmetricSourceCurve A hA H hH) t =
      (symmetricMatrixProjection n) (deriv (sourceMatrixCurve A hA H) t) :=
  (original_symmetricSourceCurve_hasDerivAt A hA H hH t).deriv

theorem original_symmetricSourceCurve_deriv_coe {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    (deriv (symmetricSourceCurve A hA H hH) t).val =
      deriv (sourceMatrixCurve A hA H) t := by
  have h := (symmetricMatrixIncl n).hasFDerivAt.comp_hasDerivAt t
    (original_symmetricSourceCurve_hasDerivAt A hA H hH t).differentiableAt.hasDerivAt
  exact h.unique ((hasDerivAt_sourceMatrixCurve A hA H t).differentiableAt.hasDerivAt)

theorem original_symmetricSourceCurve_hasDerivAt_deriv {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    HasDerivAt (deriv (symmetricSourceCurve A hA H hH))
      ((symmetricMatrixProjection n) (deriv (deriv (sourceMatrixCurve A hA H)) t)) t := by
  have hd := (symmetricMatrixProjection n).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_deriv_sourceMatrixCurve A hA H t).differentiableAt.hasDerivAt
  have he : deriv (symmetricSourceCurve A hA H hH) =
      (symmetricMatrixProjection n) ∘ deriv (sourceMatrixCurve A hA H) :=
    funext (original_symmetricSourceCurve_deriv A hA H hH)
  rw [he]
  exact hd

theorem original_symmetricSourceCurve_acceleration_coe {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (t : ℝ) :
    ((symmetricMatrixProjection n) (deriv (deriv (sourceMatrixCurve A hA H)) t)).val =
      deriv (deriv (sourceMatrixCurve A hA H)) t := by
  have hd := (symmetricMatrixIncl n).hasFDerivAt.comp_hasDerivAt t
    (original_symmetricSourceCurve_hasDerivAt_deriv A hA H hH t)
  have he : (symmetricMatrixIncl n) ∘ deriv (symmetricSourceCurve A hA H hH) =
      deriv (sourceMatrixCurve A hA H) := funext (original_symmetricSourceCurve_deriv_coe A hA H hH)
  rw [he] at hd
  exact hd.unique (hasDerivAt_deriv_sourceMatrixCurve A hA H t).differentiableAt.hasDerivAt

theorem original_sourceLogEnergy_second_diagonal {n : ℕ} (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    HasDerivAt (deriv (sourceMatrixLogEnergyCurve (exponentialDiagonal a)
      (exponentialDiagonal_posDef a) H)) (logSpectralHessianForm a H) 0 := by
  let A := exponentialDiagonal a
  let hA := exponentialDiagonal_posDef a
  let γ := symmetricSourceCurve A hA H hH
  let W := (symmetricMatrixProjection n) (deriv (deriv (sourceMatrixCurve A hA H)) 0)
  have hp (t : ℝ) : (γ t).val.PosDef := sourceMatrixCurve_posDef A hA H hH t
  have hγ (t : ℝ) : DifferentiableAt ℝ γ t :=
    (original_symmetricSourceCurve_hasDerivAt A hA H hH t).differentiableAt
  have hγ2 : HasDerivAt (deriv γ) W 0 :=
    original_symmetricSourceCurve_hasDerivAt_deriv A hA H hH 0
  have hd := original_logEnergy_second_chain_rule γ W hp hγ hγ2
  have h0 : γ 0 = symmetricMatrixDiagonal (fun i => Real.exp (a i)) := by
    apply Subtype.ext
    exact sourceMatrixCurve_zero A hA H
  have hv : (deriv γ 0).val = deriv (sourceMatrixCurve A hA H) 0 :=
    original_symmetricSourceCurve_deriv_coe A hA H hH 0
  have hw : W.val = deriv (deriv (sourceMatrixCurve A hA H)) 0 :=
    original_symmetricSourceCurve_acceleration_coe A hA H hH 0
  rw [h0, original_logEnergy_hessian_diagonal, original_logEnergy_fderiv_diagonal,
    hv, hw, diagonalLogSpectral_chain_algebra a H hH] at hd
  exact hd

theorem original_sourceLogEnergy_second {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    HasDerivAt (deriv (sourceMatrixLogEnergyCurve A hA H))
      (logSpectralHessianForm (fun i => Real.log (hA.isHermitian.eigenvalues i))
        (orthogonalConjugate (star hA.isHermitian.eigenvectorUnitary) H)) 0 := by
  let a : Fin n → ℝ := fun i => Real.log (hA.isHermitian.eigenvalues i)
  let U := hA.isHermitian.eigenvectorUnitary
  let H' := orthogonalConjugate (star U) H
  have hH' : H'.IsSymm := orthogonalConjugate_isSymm (star U) H hH
  have he : exponentialDiagonal a = Matrix.diagonal hA.isHermitian.eigenvalues := by
    unfold exponentialDiagonal
    apply congrArg Matrix.diagonal
    funext i
    exact Real.exp_log (hA.eigenvalues_pos i)
  have hf : sourceMatrixLogEnergyCurve A hA H =
      sourceMatrixLogEnergyCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H' := by
    funext t
    simpa only [he, H', U] using sourceMatrixLogEnergyCurve_eigenbasis A hA H hH t
  rw [hf]
  exact original_sourceLogEnergy_second_diagonal a H' hH'

theorem original_sourceLogEnergy_second_ge {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    8 * (matrixFullHSNorm H)^2 ≤ deriv (deriv (sourceMatrixLogEnergyCurve A hA H)) 0 := by
  rw [(original_sourceLogEnergy_second A hA H hH).deriv]
  have h := logSpectralHessianForm_ge_HS
    (fun i => Real.log (hA.isHermitian.eigenvalues i))
    (orthogonalConjugate (star hA.isHermitian.eigenvectorUnitary) H)
    (orthogonalConjugate_isSymm _ H hH)
  rwa [matrixFullHSNorm_orthogonalConjugate _ H hH] at h


theorem original_logEnergy_hasFDerivAt_fderiv {n : ℕ}
    (A : SymmetricMatrix n) (hA : A.val.PosDef) :
    HasFDerivAt (fderiv ℝ (symmetricLogEnergy (n := n))) (originalLogEnergyHessian A) A := by
  exact ((contDiffAt_symmetricLogEnergy A hA).fderiv_right
    (m := ⊤) (by simp)).differentiableAt (by simp) |>.hasFDerivAt

theorem original_logEnergy_hessian_of_eigenbasis {n : ℕ}
    (A V : SymmetricMatrix n) (hA : A.val.PosDef)
    (U : unitary (Matrix (Fin n) (Fin n) ℝ)) (a : Fin n → ℝ)
    (hdiag : orthogonalConjugate (star U) A.val = exponentialDiagonal a) :
    originalLogEnergyHessian A V V =
      diagonalLogSpectralHessian a (orthogonalConjugate (star U) V.val) := by
  have he : symmetricOrthogonalConjugateEquiv (star U) A =
      symmetricMatrixDiagonal (fun i => Real.exp (a i)) := by
    apply Subtype.ext
    exact hdiag
  rw [← original_logEnergy_hessian_conjugate (star U) A V hA, he]
  exact original_logEnergy_hessian_diagonal a (symmetricOrthogonalConjugateEquiv (star U) V)

end PaperI
