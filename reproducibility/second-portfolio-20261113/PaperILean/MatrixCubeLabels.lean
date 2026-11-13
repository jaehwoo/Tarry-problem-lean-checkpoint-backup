import PaperILean.AnisotropicSkewBounds
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators

/-! I333-336: entry cubes for real 3 by 3 matrices. A translated floor label
handles the closed box endpoints without pretending that the cubes are closed.
The labels and their counting bounds do not depend on any frame or shape. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def matrixCubeLabel (M δ : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℤ := fun i j => ⌊(A i j + M) / δ⌋

def matrixCubeCoordinateLabels (M δ : ℝ) : Finset ℤ :=
  Finset.Icc 0 ⌊2 * M / δ⌋

def matrixCubeLabels (M δ : ℝ) : Finset (Matrix (Fin 3) (Fin 3) ℤ) :=
  Fintype.piFinset fun _ : Fin 3 =>
    Fintype.piFinset fun _ : Fin 3 => matrixCubeCoordinateLabels M δ

theorem abs_sub_lt_of_translated_floor_eq (M δ x y : ℝ) (hδ : 0 < δ)
    (h : ⌊(x + M) / δ⌋ = ⌊(y + M) / δ⌋) : |x - y| < δ := by
  have h' := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, show x + M - (y + M) = x - y by ring,
    abs_div, abs_of_pos hδ] at h'
  simpa using (div_lt_iff₀ hδ).mp h'

theorem matrixCubeLabel_mem (M δ : ℝ) (hδ : 0 < δ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ‖A‖ ≤ M) :
    matrixCubeLabel M δ A ∈ matrixCubeLabels M δ := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Fintype.mem_piFinset.mpr
  intro j
  have h := (matrix_entry_abs_le_opNorm A i j).trans hA
  have hx := abs_le.mp h
  apply Finset.mem_Icc.mpr
  constructor
  · exact Int.floor_nonneg.mpr (div_nonneg (by linarith) hδ.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ.le)

theorem matrixCubeLabel_eq_opNorm_sub_le (M δ : ℝ) (hδ : 0 < δ)
    (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (h : matrixCubeLabel M δ A = matrixCubeLabel M δ B) :
    ‖B - A‖ ≤ 3 * δ := by
  apply matrix_opNorm_le_three_mul_entry_bound _ δ hδ.le
  intro i j
  exact (abs_sub_lt_of_translated_floor_eq M δ (B i j) (A i j) hδ
    (congrArg (fun C : Matrix (Fin 3) (Fin 3) ℤ => C i j) h.symm)).le

theorem matrixCubeCoordinateLabels_card_le (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) :
    ((matrixCubeCoordinateLabels M δ).card : ℝ) ≤ 2 * M / δ + 1 := by
  have hn : (0 : ℤ) ≤ ⌊2 * M / δ⌋ := Int.floor_nonneg.mpr (by positivity)
  have hc : ((matrixCubeCoordinateLabels M δ).card : ℤ) = ⌊2 * M / δ⌋ + 1 := by
    simpa [matrixCubeCoordinateLabels] using
      (Int.card_Icc_of_le (a := 0) (b := ⌊2 * M / δ⌋) (by omega))
  have hc' : ((matrixCubeCoordinateLabels M δ).card : ℝ) =
      (⌊2 * M / δ⌋ : ℝ) + 1 := by exact_mod_cast hc
  rw [hc']
  exact add_le_add_right (Int.floor_le _) _

theorem matrixCubeLabels_card (M δ : ℝ) :
    (matrixCubeLabels M δ).card = (matrixCubeCoordinateLabels M δ).card ^ 9 := by
  calc
    (matrixCubeLabels M δ).card =
        ((matrixCubeCoordinateLabels M δ).card ^ 3) ^ 3 :=
      (Fintype.card_piFinset_const _ 3).trans
        (congrArg (fun n : ℕ => n ^ 3) (Fintype.card_piFinset_const _ 3))
    _ = (matrixCubeCoordinateLabels M δ).card ^ 9 := by ring

theorem matrixCubeLabels_card_le (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) :
    ((matrixCubeLabels M δ).card : ℝ) ≤ (2 * M / δ + 1) ^ 9 := by
  rw [matrixCubeLabels_card, Nat.cast_pow]
  exact pow_le_pow_left₀ (by positivity) (matrixCubeCoordinateLabels_card_le M δ hM hδ) _

end PaperI
