import PaperILean.TensorContractionBounds
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.NormedSpace.Multilinear.Basic

/-! The literal determinant perturbation estimate at I1480[534,674)
and I1481-I1483. Rows carry the manuscript's Euclidean norm. Hadamard's
inequality has constant one, so the final constant is exactly n. -/

noncomputable section
open scoped BigOperators

namespace PaperI.DeterminantRowPerturbation

/-- The row determinant with the Euclidean row space retained. -/
def euclideanRowDeterminant (n : ℕ) :
    MultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ (Fin n)) ℝ :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det.toMultilinearMap

theorem euclideanRowDeterminant_apply (n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    euclideanRowDeterminant n v = Matrix.det (fun i j => v i j) := by
  change Matrix.det ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix v) = _
  change Matrix.det (fun i j => v j i) = _
  exact Matrix.det_transpose (fun i j => v i j)

/-- Hadamard's exact product bound, including the empty determinant. -/
theorem euclideanRowDeterminant_norm_le (n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    ‖euclideanRowDeterminant n v‖ ≤ ∏ i, ‖v i‖ := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) :=
    ⟨finrank_euclideanSpace_fin⟩
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have h := b.toBasis.orientation.abs_volumeForm_apply_le v
  rw [b.toBasis.orientation.volumeForm_robust b rfl] at h
  simpa only [Real.norm_eq_abs, euclideanRowDeterminant, b] using h

/-- Full row perturbation bound, with the original factor n and no factorial
loss. The zero-dimensional case is retained. -/
theorem determinant_row_perturbation_of_nonneg (n : ℕ)
    (B A : Matrix (Fin n) (Fin n) ℝ) (M eps : ℝ)
    (hM : 0 ≤ M) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hB : ∀ i, coordinateL2Norm (B i) ≤ M)
    (herror : ∀ i, coordinateL2Norm (A i - B i) ≤ eps) :
    |A.det - B.det| ≤ (n : ℝ) * eps * (M + 1) ^ (n - 1) := by
  classical
  let a : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun i => (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm (A i)
  let b : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun i => (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm (B i)
  have hb : ∀ i, ‖b i‖ ≤ M := by
    intro i
    simpa only [b, coordinateL2Norm_eq_norm] using hB i
  have he : ∀ i, ‖a i - b i‖ ≤ eps := by
    intro i
    simpa only [a, b, coordinateL2Norm_eq_norm, map_sub] using herror i
  have ha : ∀ i, ‖a i‖ ≤ M + 1 := by
    intro i
    calc
      ‖a i‖ = ‖(a i - b i) + b i‖ := by rw [sub_add_cancel]
      _ ≤ ‖a i - b i‖ + ‖b i‖ := norm_add_le _ _
      _ ≤ eps + M := add_le_add (he i) (hb i)
      _ ≤ M + 1 := by linarith
  have hM1 : 0 ≤ M + 1 := by linarith
  have han : ‖a‖ ≤ M + 1 := (pi_norm_le_iff_of_nonneg hM1).mpr ha
  have hbn : ‖b‖ ≤ M + 1 := (pi_norm_le_iff_of_nonneg hM1).mpr
    (fun i => (hb i).trans (by linarith))
  have hen : ‖a - b‖ ≤ eps := (pi_norm_le_iff_of_nonneg heps).mpr he
  have h := (euclideanRowDeterminant n).norm_image_sub_le_of_bound
    (show (0 : ℝ) ≤ 1 by norm_num)
    (fun v => by simpa only [one_mul] using euclideanRowDeterminant_norm_le n v) a b
  have hpow : max ‖a‖ ‖b‖ ^ (n - 1) ≤ (M + 1) ^ (n - 1) :=
    pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg a)) (max_le han hbn) _
  have hbound : ‖euclideanRowDeterminant n a - euclideanRowDeterminant n b‖ ≤
      (n : ℝ) * eps * (M + 1) ^ (n - 1) := by
    calc
      _ ≤ (n : ℝ) * max ‖a‖ ‖b‖ ^ (n - 1) * ‖a - b‖ := by
        simpa only [Fintype.card_fin, one_mul] using h
      _ ≤ (n : ℝ) * (M + 1) ^ (n - 1) * eps :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)) hen
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hM1 _))
      _ = _ := by ring
  simpa only [euclideanRowDeterminant_apply, a, b, Real.norm_eq_abs] using hbound

/-- The manuscript row bound without extra assumptions in dimension zero.
For a positive dimension the row bounds themselves force both tolerances
to be nonnegative; for an empty matrix both determinants equal one. -/
theorem determinant_row_perturbation (n : ℕ)
    (B A : Matrix (Fin n) (Fin n) ℝ) (M eps : ℝ)
    (heps1 : eps ≤ 1)
    (hB : ∀ i, coordinateL2Norm (B i) ≤ M)
    (herror : ∀ i, coordinateL2Norm (A i - B i) ≤ eps) :
    |A.det - B.det| ≤ (n : ℝ) * eps * (M + 1) ^ (n - 1) := by
  cases n with
  | zero => simp only [Matrix.det_isEmpty, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ n =>
      exact determinant_row_perturbation_of_nonneg (n + 1) B A M eps
        ((coordinateL2Norm_nonneg (B 0)).trans (hB 0))
        ((coordinateL2Norm_nonneg (A 0 - B 0)).trans (herror 0))
        heps1 hB herror

end PaperI.DeterminantRowPerturbation
