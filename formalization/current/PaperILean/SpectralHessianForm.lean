import PaperILean.SpectralCothKernel
import PaperILean.TensorContractionBounds
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! The exact finite spectral expression in Paper I lines214-223.
The HS norm includes every ordered matrix entry. Symmetry is an explicit source
hypothesis. This algebraic lower bound does not prove the unformalized equality
between the expression and the actual second derivative of matrix log energy.
-/

noncomputable section
open scoped BigOperators
namespace PaperI

def matrixFullHSNorm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  coordinateL2Norm (fun p : Fin n × Fin n => H p.1 p.2)

def logSpectralHessianForm {n : ℕ} (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  8 * ∑ i, (H i i) ^ 2 +
    16 * ∑ i, ∑ j, if i < j then
      spectralCothKernel ((a i - a j) / 2) * (H i j) ^ 2 else 0

theorem matrixFullHSNorm_nonneg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ matrixFullHSNorm H := coordinateL2Norm_nonneg _

theorem matrixFullHSNorm_sq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) :
    (matrixFullHSNorm H) ^ 2 = ∑ i, ∑ j, (H i j) ^ 2 := by
  rw [matrixFullHSNorm, coordinateL2Norm_sq, Fintype.sum_prod_type]

theorem matrixFullHSNorm_eq_zero_iff {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) :
    matrixFullHSNorm H = 0 ↔ H = 0 := by
  constructor
  · intro h
    rw [matrixFullHSNorm, coordinateL2Norm_eq_norm] at h
    have he := norm_eq_zero.mp h
    have hv : (fun p : Fin n × Fin n => H p.1 p.2) = 0 := by
      have hmap := congrArg (WithLp.linearEquiv 2 ℝ ((Fin n × Fin n) → ℝ)) he
      simpa using hmap
    apply Matrix.ext
    intro i j
    exact congrFun hv (i, j)
  · intro h
    simp [h, matrixFullHSNorm, coordinateL2Norm]

theorem symmetric_matrix_square_sum_split {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (∑ i, ∑ j, (H i j) ^ 2) =
      (∑ i, (H i i) ^ 2) + 2 * ∑ i, ∑ j, if i < j then (H i j) ^ 2 else 0 := by
  have hgt : (∑ i, ∑ j, if j < i then (H i j) ^ 2 else 0) =
      ∑ i, ∑ j, if i < j then (H i j) ^ 2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hH.apply i j]
  have htri (i j : Fin n) : (H i j) ^ 2 =
      (if i = j then (H i j) ^ 2 else 0) +
      (if i < j then (H i j) ^ 2 else 0) +
      (if j < i then (H i j) ^ 2 else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, ne_of_lt hij, not_lt_of_ge hij.le]
    · subst j; simp
    · simp [hij, (ne_of_lt hij).symm, not_lt_of_ge hij.le]
  calc
    _ = ∑ i, ∑ j, ((if i = j then (H i j) ^ 2 else 0) +
        (if i < j then (H i j) ^ 2 else 0) +
        (if j < i then (H i j) ^ 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun j _ => htri i j)
    _ = (∑ i, (H i i) ^ 2) +
        (∑ i, ∑ j, if i < j then (H i j) ^ 2 else 0) +
        (∑ i, ∑ j, if j < i then (H i j) ^ 2 else 0) := by
      simp [Finset.sum_add_distrib]
    _ = _ := by rw [hgt]; ring

theorem logSpectralHessianForm_ge_HS {n : ℕ} (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    8 * (matrixFullHSNorm H) ^ 2 ≤ logSpectralHessianForm a H := by
  have hu : (∑ i, ∑ j, if i < j then (H i j) ^ 2 else 0) ≤
      ∑ i, ∑ j, if i < j then
        spectralCothKernel ((a i - a j) / 2) * (H i j) ^ 2 else 0 := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    by_cases hij : i < j
    · simp only [if_pos hij]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (spectralCothKernel_ge_one ((a i - a j) / 2)) (sq_nonneg (H i j))
    · simp only [if_neg hij, le_refl]
  rw [matrixFullHSNorm_sq, symmetric_matrix_square_sum_split H hH]
  unfold logSpectralHessianForm
  nlinarith

theorem logSpectralHessianForm_nonneg {n : ℕ} (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    0 ≤ logSpectralHessianForm a H :=
  (mul_nonneg (by norm_num) (sq_nonneg _)).trans (logSpectralHessianForm_ge_HS a H hH)

theorem logSpectralHessianForm_pos {n : ℕ} (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hne : H ≠ 0) :
    0 < logSpectralHessianForm a H := by
  have hn : matrixFullHSNorm H ≠ 0 := fun h => hne ((matrixFullHSNorm_eq_zero_iff H).mp h)
  have hp : 0 < matrixFullHSNorm H := lt_of_le_of_ne (matrixFullHSNorm_nonneg H) hn.symm
  exact (mul_pos (by norm_num) (pow_pos hp 2)).trans_le (logSpectralHessianForm_ge_HS a H hH)

theorem logSpectralHessianForm_zero {n : ℕ} (a : Fin n → ℝ) :
    logSpectralHessianForm a 0 = 0 := by
  simp [logSpectralHessianForm]

theorem logSpectralHessianForm_constant_spectrum {n : ℕ} (s : ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    logSpectralHessianForm (fun _ => s) H = 8 * (matrixFullHSNorm H) ^ 2 := by
  rw [matrixFullHSNorm_sq, symmetric_matrix_square_sum_split H hH]
  simp only [logSpectralHessianForm, sub_self, zero_div, spectralCothKernel_zero, one_mul]
  ring

theorem continuous_logSpectralHessianForm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun a : Fin n → ℝ => logSpectralHessianForm a H) := by
  unfold logSpectralHessianForm
  apply Continuous.add continuous_const
  apply continuous_const.mul
  apply continuous_finset_sum
  intro i hi
  apply continuous_finset_sum
  intro j hj
  by_cases hij : i < j
  · simp only [if_pos hij]
    exact (continuous_spectralCothKernel.comp
      (((continuous_apply i).sub (continuous_apply j)).div_const 2)).mul continuous_const
  · simp only [if_neg hij]
    exact continuous_const

theorem logSpectralHessianForm_scaled_ge_HS {n : ℕ} (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (lam : ℝ) (hLam : 0 ≤ lam) :
    8 * lam * (matrixFullHSNorm H) ^ 2 ≤ lam * logSpectralHessianForm a H := by
  have h := mul_le_mul_of_nonneg_left (logSpectralHessianForm_ge_HS a H hH) hLam
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

theorem logSpectralHessianForm_scaled_pos {n : ℕ} (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hne : H ≠ 0)
    (lam : ℝ) (hLam : 0 < lam) : 0 < lam * logSpectralHessianForm a H :=
  mul_pos hLam (logSpectralHessianForm_pos a H hH hne)

end PaperI
