import PaperILean.RotationNeighborhoods

/-! I327-329: the anisotropic skew-entry box, with fixed explicit constants.
All positive lengths are allowed; ordering is not needed for these estimates.
Open norm balls and closed entry boxes are distinguished by radius factors. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def positiveDiagonalFrame (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) : PositiveFrame :=
  ⟨Matrix.diagonal e, by rw [Matrix.det_diagonal]; exact Finset.prod_pos (fun i _ => he i)⟩

def diagonalFrameConjugate (e : Fin 3 → ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ) :=
  (Matrix.diagonal e)⁻¹ * H * Matrix.diagonal e

theorem diagonalFrameConjugate_eq_frameConjugate (e : Fin 3 → ℝ)
    (he : ∀ i, 0 < e i) (H : Matrix (Fin 3) (Fin 3) ℝ) :
    diagonalFrameConjugate e H = frameConjugate (positiveDiagonalFrame e he) H := rfl

theorem positive_diagonal_inverse (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) :
    (Matrix.diagonal e)⁻¹ = Matrix.diagonal (fun i => (e i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j; simp [Matrix.diagonal, (he i).ne']
  · simp [Matrix.diagonal, hij]

theorem diagonalFrameConjugate_apply (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    diagonalFrameConjugate e H i j = H i j * (e j / e i) := by
  rw [diagonalFrameConjugate, positive_diagonal_inverse e he]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

theorem diagonalFrameConjugate_abs_apply (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    |diagonalFrameConjugate e H i j| = |H i j| * (e j / e i) := by
  rw [diagonalFrameConjugate_apply e he, abs_mul, abs_of_pos (div_pos (he j) (he i))]

theorem skew_matrix_diagonal_zero (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : Hᵀ = -H)
    (i : Fin 3) : H i i = 0 := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i i) hH
  change H i i = -H i i at h
  linarith

theorem skew_matrix_abs_apply_comm (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : Hᵀ = -H)
    (i j : Fin 3) : |H j i| = |H i j| := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i j) hH
  change H j i = -H i j at h
  rw [h, abs_neg]

theorem matrix_opNorm_le_three_mul_entry_bound (A : Matrix (Fin 3) (Fin 3) ℝ)
    (t : ℝ) (ht : 0 ≤ t) (hA : ∀ i j, |A i j| ≤ t) : ‖A‖ ≤ 3 * t := by
  apply (matrix_opNorm_le_fullHS A).trans
  apply (sq_le_sq₀ (matrixFullHSNorm_nonneg A) (by positivity : 0 ≤ 3 * t)).mp
  rw [matrixFullHSNorm_sq]
  have hsq (i j : Fin 3) : (A i j)^2 ≤ t^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ht).mpr (hA i j)
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, (A i j)^2) ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, t^2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hsq i j))
    _ = (3 * t)^2 := by simp; ring

theorem skew_weighted_entry_le_of_opNorm_le (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : Hᵀ = -H) (t : ℝ)
    (hn : ‖diagonalFrameConjugate e H‖ ≤ t) (i j : Fin 3) :
    |H i j| ≤ t * min (e i / e j) (e j / e i) := by
  have hentry (a b : Fin 3) : |H a b| ≤ t * (e a / e b) := by
    have h := (matrix_entry_abs_le_opNorm (diagonalFrameConjugate e H) a b).trans hn
    rw [diagonalFrameConjugate_abs_apply e he] at h
    have hh := (le_div_iff₀ (div_pos (he b) (he a))).mpr h
    convert hh using 1 <;> field_simp <;> ring
  have h1 := hentry i j
  have h2 := hentry j i
  rw [skew_matrix_abs_apply_comm H hH i j] at h2
  rcases le_total (e i / e j) (e j / e i) with h | h
  · rw [min_eq_left h]; exact h1
  · rw [min_eq_right h]; exact h2

theorem skew_weighted_upper_bound_all (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : Hᵀ = -H) (t : ℝ) (ht : 0 ≤ t)
    (hb : ∀ i j : Fin 3, i < j → |H i j| ≤ t * min (e i / e j) (e j / e i)) :
    ∀ i j : Fin 3, |H i j| ≤ t * min (e i / e j) (e j / e i) := by
  intro i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hb i j hij
  · subst j
    rw [skew_matrix_diagonal_zero H hH, abs_zero]
    exact mul_nonneg ht (le_min (div_nonneg (he i).le (he i).le) (div_nonneg (he i).le (he i).le))
  · rw [skew_matrix_abs_apply_comm H hH j i, min_comm]
    exact hb j i hij

theorem diagonalFrameConjugate_entry_le_of_weighted_bound
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (t : ℝ) (ht : 0 ≤ t)
    (hb : ∀ i j : Fin 3, |H i j| ≤ t * min (e i / e j) (e j / e i)) :
    ∀ i j : Fin 3, |diagonalFrameConjugate e H i j| ≤ t := by
  intro i j
  rw [diagonalFrameConjugate_abs_apply e he]
  have hh := (hb i j).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) ht)
  calc
    |H i j| * (e j / e i) ≤ (t * (e i / e j)) * (e j / e i) :=
      mul_le_mul_of_nonneg_right hh (div_pos (he j) (he i)).le
    _ = t := by field_simp [(he i).ne', (he j).ne']

theorem skew_opNorm_le_of_weighted_upper_bound
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : Hᵀ = -H) (t : ℝ) (ht : 0 ≤ t)
    (hb : ∀ i j : Fin 3, i < j → |H i j| ≤ t * min (e i / e j) (e j / e i)) :
    ‖diagonalFrameConjugate e H‖ ≤ 3 * t :=
  matrix_opNorm_le_three_mul_entry_bound _ t ht
    (diagonalFrameConjugate_entry_le_of_weighted_bound e he H t ht
      (skew_weighted_upper_bound_all e he H hH t ht hb))

def anisotropicSkewBox (e : Fin 3 → ℝ) (t : ℝ) : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {H | Hᵀ = -H ∧ ∀ i j : Fin 3, i < j → |H i j| ≤ t * min (e i / e j) (e j / e i)}

def anisotropicSkewBall (e : Fin 3 → ℝ) (t : ℝ) : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {H | Hᵀ = -H ∧ ‖diagonalFrameConjugate e H‖ < t}

theorem anisotropicSkewBall_subset_box (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) :
    anisotropicSkewBall e t ⊆ anisotropicSkewBox e t := by
  rintro H ⟨hH, hn⟩
  exact ⟨hH, fun i j _ => skew_weighted_entry_le_of_opNorm_le e he H hH t hn.le i j⟩

theorem anisotropicSkewBox_opNorm_bound (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : 0 ≤ t) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H ∈ anisotropicSkewBox e t) : ‖diagonalFrameConjugate e H‖ ≤ 3 * t :=
  skew_opNorm_le_of_weighted_upper_bound e he H hH.1 t ht hH.2

theorem anisotropicSkewBox_quarter_subset_ball (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : 0 < t) : anisotropicSkewBox e (t/4) ⊆ anisotropicSkewBall e t := by
  intro H hH
  refine ⟨hH.1, ?_⟩
  have h := anisotropicSkewBox_opNorm_bound e he (t/4) (by positivity) H hH
  linarith

theorem ordered_positive_ratio_le_reverse (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) : a / b ≤ b / a := by
  apply (div_le_div_iff₀ hb ha).mpr
  nlinarith

end PaperI
