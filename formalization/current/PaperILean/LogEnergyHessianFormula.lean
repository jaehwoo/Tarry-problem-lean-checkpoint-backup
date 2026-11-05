import PaperILean.LogEnergySourceHessian
import PaperILean.OriginalSpectralHessian

/-! Exact source second derivative and lower bound at arbitrary real SPD A.
The earlier helpers retain the alternative first-variation calculation.
The general source theorem uses the genuine log-square Fréchet Hessian and
second chain rule formalized in OriginalSpectralHessian. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI
set_option maxHeartbeats 400000

theorem sourcePositiveSqrt_exponentialDiagonal_inv {n : ℕ} (a : Fin n → ℝ) :
    (sourcePositiveSqrt (exponentialDiagonal a) (exponentialDiagonal_posDef a))⁻¹ =
      Matrix.diagonal (fun i => Real.exp (-a i / 2)) := by
  apply Matrix.inv_eq_left_inv
  rw [sourcePositiveSqrt_exponentialDiagonal, Matrix.diagonal_mul_diagonal]
  have he : (fun i => Real.exp (-a i / 2) * Real.exp (a i / 2)) = fun _ => (1 : ℝ) := by
    funext i
    rw [← Real.exp_add, show -a i / 2 + a i / 2 = 0 by ring, Real.exp_zero]
  rw [he, Matrix.diagonal_one]

theorem sourceRightGenerator_exponentialDiagonal_entry {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    sourceRightGenerator (exponentialDiagonal a) (exponentialDiagonal_posDef a) H i j =
      Real.exp ((a j - a i) / 2) * H i j := by
  rw [sourceRightGenerator, sourcePositiveSqrt_exponentialDiagonal_inv,
    sourcePositiveSqrt_exponentialDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [show (a j - a i) / 2 = -a i / 2 + a j / 2 by ring, Real.exp_add]
  ring

theorem sourceDiagonalLogVelocity_entry {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (i j : Fin n) :
    sourceDiagonalLogVelocity a H i j =
      (expDividedDifference (a i) (a j))⁻¹ *
        (2 * Real.exp ((a i + a j) / 2) * H i j) := by
  change (diagonalExpDifferentialEquiv a).symm
    ((symmetricMatrixProjection n)
      (deriv (sourceMatrixCurve (exponentialDiagonal a) (exponentialDiagonal_posDef a) H) 0) :
        Matrix (Fin n) (Fin n) ℝ) i j = _
  rw [diagonalExpDifferentialEquiv_symm_apply,
    symmetricSourceCurve_velocity_coe _ _ H hH,
    sourceMatrixCurve_exponentialDiagonal_first_entry]

theorem source_log_second_trace_sum {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    4 * Matrix.trace (sourceDiagonalLogVelocity a H *
      sourceRightGenerator (exponentialDiagonal a) (exponentialDiagonal_posDef a) H) =
      ∑ i, ∑ j, 8 * Real.exp (a i) * (expDividedDifference (a i) (a j))⁻¹ * (H i j)^2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [sourceDiagonalLogVelocity_entry a H hH, sourceRightGenerator_exponentialDiagonal_entry,
    hH.apply i j]
  have he : Real.exp ((a i + a j) / 2) * Real.exp ((a i - a j) / 2) = Real.exp (a i) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = 8 * (Real.exp ((a i + a j) / 2) * Real.exp ((a i - a j) / 2)) *
        (expDividedDifference (a i) (a j))⁻¹ * (H i j)^2 := by ring
    _ = _ := by rw [he]

theorem sum_ordered_pairs_split {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) +
      ∑ i, ∑ j, if i < j then f i j + f j i else 0 := by
  have hgt : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f j i else 0 := by rw [Finset.sum_comm]
  have ht (i j : Fin n) : f i j = (if i = j then f i j else 0) +
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, (ne_of_lt h).symm, not_lt_of_ge h.le]
  calc
    _ = ∑ i, ∑ j, ((if i = j then f i j else 0) +
      (if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_congr rfl (fun j _ => ht i j)
    _ = (∑ i, f i i) + (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by simp [Finset.sum_add_distrib]
    _ = _ := by
      rw [hgt, add_assoc, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp

theorem expDividedDifference_source_pair_coefficient (a b : ℝ) :
    8 * (Real.exp a + Real.exp b) * (expDividedDifference a b)⁻¹ =
      16 * spectralCothKernel ((a-b)/2) := by
  by_cases hab : a = b
  · subst b
    rw [expDividedDifference_self]
    simp only [sub_self, zero_div, spectralCothKernel_zero]
    field_simp
    ring
  · rw [spectralCothKernel_half_difference_of_ne a b hab]
    simp only [expDividedDifference, hab, if_false]
    have he : Real.exp a - Real.exp b ≠ 0 := sub_ne_zero.mpr (fun h => hab (Real.exp_injective h))
    field_simp
    ring

theorem source_log_second_trace_eq_spectral {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    4 * Matrix.trace (sourceDiagonalLogVelocity a H *
      sourceRightGenerator (exponentialDiagonal a) (exponentialDiagonal_posDef a) H) =
      logSpectralHessianForm a H := by
  rw [source_log_second_trace_sum a H hH, sum_ordered_pairs_split]
  unfold logSpectralHessianForm
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [expDividedDifference_self]
    field_simp
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [if_pos hij]
      rw [expDividedDifference_symm (a j) (a i), hH.apply i j]
      calc
        _ = (8 * (Real.exp (a i) + Real.exp (a j)) *
          (expDividedDifference (a i) (a j))⁻¹) * (H i j)^2 := by ring
        _ = _ := by rw [expDividedDifference_source_pair_coefficient]; ring
    · simp only [if_neg hij, mul_zero]

theorem hasDerivAt_deriv_logEnergy_exponentialDiagonal {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    HasDerivAt (deriv (sourceMatrixLogEnergyCurve (exponentialDiagonal a)
      (exponentialDiagonal_posDef a) H)) (logSpectralHessianForm a H) 0 := by
  rw [← source_log_second_trace_eq_spectral a H hH]
  exact hasDerivAt_deriv_logEnergy_exponentialDiagonal_trace a H hH

theorem hasDerivAt_deriv_sourceMatrixLogEnergyCurve_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    HasDerivAt (deriv (sourceMatrixLogEnergyCurve A hA H))
      (logSpectralHessianForm (fun i => Real.log (hA.isHermitian.eigenvalues i))
        (orthogonalConjugate (star hA.isHermitian.eigenvectorUnitary) H)) 0 := by
  exact original_sourceLogEnergy_second A hA H hH

theorem sourceMatrixLogEnergyCurve_second_derivative_ge_HS {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    8 * (matrixFullHSNorm H)^2 ≤ deriv (deriv (sourceMatrixLogEnergyCurve A hA H)) 0 := by
  rw [(hasDerivAt_deriv_sourceMatrixLogEnergyCurve_zero A hA H hH).deriv]
  have h := logSpectralHessianForm_ge_HS
    (fun i => Real.log (hA.isHermitian.eigenvalues i))
    (orthogonalConjugate (star hA.isHermitian.eigenvectorUnitary) H)
    (orthogonalConjugate_isSymm _ H hH)
  rwa [matrixFullHSNorm_orthogonalConjugate _ H hH] at h

theorem sourceMatrixLogEnergyCurve_second_derivative_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    deriv (deriv (sourceMatrixLogEnergyCurve A hA H)) 0 =
      logSpectralHessianForm (fun i => Real.log (hA.isHermitian.eigenvalues i))
        (orthogonalConjugate (star hA.isHermitian.eigenvectorUnitary) H) :=
  (hasDerivAt_deriv_sourceMatrixLogEnergyCurve_zero A hA H hH).deriv

theorem sourceMatrixLogEnergyCurve_second_derivative_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hne : H ≠ 0) :
    0 < deriv (deriv (sourceMatrixLogEnergyCurve A hA H)) 0 := by
  have hn : matrixFullHSNorm H ≠ 0 := fun h => hne ((matrixFullHSNorm_eq_zero_iff H).mp h)
  have hp : 0 < matrixFullHSNorm H := lt_of_le_of_ne (matrixFullHSNorm_nonneg H) hn.symm
  exact (mul_pos (by norm_num) (pow_pos hp 2)).trans_le
    (sourceMatrixLogEnergyCurve_second_derivative_ge_HS A hA H hH)

end PaperI
