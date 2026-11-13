import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic

/-! I668--694: qualitative Euclidean singular values of a rectangular real matrix.
The list has one entry per domain coordinate, including zero entries, and is
ordered decreasingly by a permutation. No quantitative uniform bound is asserted.
-/

noncomputable section
open scoped Matrix
namespace PaperI

variable {m : Type*} [Fintype m] {n : ℕ}

/-- The unsorted square roots of the eigenvalues of the actual right Gram matrix. -/
def rectangularSingularValues (A : Matrix m (Fin n) ℝ) (i : Fin n) : ℝ :=
  Real.sqrt ((Matrix.isHermitian_transpose_mul_self A).eigenvalues i)

theorem rectangularSingularValues_nonneg (A : Matrix m (Fin n) ℝ) (i : Fin n) :
    0 ≤ rectangularSingularValues A i := Real.sqrt_nonneg _

theorem rectangularSingularValues_sq (A : Matrix m (Fin n) ℝ) (i : Fin n) :
    rectangularSingularValues A i ^ 2 =
      (Matrix.isHermitian_transpose_mul_self A).eigenvalues i :=
  Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)

theorem rectangularSingularValues_pos_iff (A : Matrix m (Fin n) ℝ) (i : Fin n) :
    0 < rectangularSingularValues A i ↔
      (Matrix.isHermitian_transpose_mul_self A).eigenvalues i ≠ 0 := by
  rw [rectangularSingularValues, Real.sqrt_pos]
  exact (lt_iff_le_and_ne).trans (by
    simp [Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i, ne_comm])

/-- Permutation sorting the singular values decreasingly, retaining multiplicity. -/
def singularValueOrder (A : Matrix m (Fin n) ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (α := OrderDual ℝ) (rectangularSingularValues A)

def descendingSingularValues (A : Matrix m (Fin n) ℝ) (i : Fin n) : ℝ :=
  rectangularSingularValues A (singularValueOrder A i)

theorem descendingSingularValues_nonneg (A : Matrix m (Fin n) ℝ) (i : Fin n) :
    0 ≤ descendingSingularValues A i := rectangularSingularValues_nonneg A _

theorem descendingSingularValues_antitone (A : Matrix m (Fin n) ℝ) :
    Antitone (descendingSingularValues A) :=
  Tuple.monotone_sort (α := OrderDual ℝ) (rectangularSingularValues A)

theorem descendingSingularValues_sq (A : Matrix m (Fin n) ℝ) (i : Fin n) :
    descendingSingularValues A i ^ 2 =
      (Matrix.isHermitian_transpose_mul_self A).eigenvalues (singularValueOrder A i) :=
  rectangularSingularValues_sq A _

theorem descendingSingularValues_permutation (A : Matrix m (Fin n) ℝ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i,
      descendingSingularValues A i = rectangularSingularValues A (σ i) :=
  ⟨singularValueOrder A, fun _ => rfl⟩

theorem descendingSingularValues_unique (A : Matrix m (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (hσ : Antitone (rectangularSingularValues A ∘ σ)) :
    rectangularSingularValues A ∘ σ = descendingSingularValues A :=
  Tuple.unique_antitone hσ (descendingSingularValues_antitone A)

theorem rank_eq_card_positive_rectangularSingularValues (A : Matrix m (Fin n) ℝ) :
    A.rank = Fintype.card {i // 0 < rectangularSingularValues A i} := by
  classical
  have hgram : (Aᴴ * A).rank = A.rank := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.rank_transpose_mul_self A
  rw [← hgram, (Matrix.isHermitian_transpose_mul_self A).rank_eq_card_non_zero_eigs]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i =>
    (rectangularSingularValues_pos_iff A i).symm)

theorem rank_eq_card_positive_descendingSingularValues (A : Matrix m (Fin n) ℝ) :
    A.rank = Fintype.card {i // 0 < descendingSingularValues A i} := by
  classical
  rw [rank_eq_card_positive_rectangularSingularValues]
  exact (Fintype.card_congr ((singularValueOrder A).subtypeEquiv
    (fun _ => Iff.rfl))).symm

/-- Positive entries of a decreasing list form its initial segment. -/
theorem antitone_pos_iff_lt_card {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f) (j : Fin n) :
    0 < f j ↔ j.val < Fintype.card {i // 0 < f i} := by
  classical
  rw [Fintype.card_subtype]
  constructor
  · intro hj
    have hsub : Finset.Iic j ⊆ Finset.univ.filter (fun i => 0 < f i) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj.trans_le (hf (Finset.mem_Iic.mp hi))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
  · intro hj
    by_contra hnot
    have hsub : Finset.univ.filter (fun i => 0 < f i) ⊆ Finset.Iio j := by
      intro i hi
      apply Finset.mem_Iio.mpr
      by_contra hn
      have hi' : 0 < f i := (Finset.mem_filter.mp hi).2
      exact hnot (hi'.trans_le (hf (le_of_not_gt hn)))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega

theorem descendingSingularValues_pos_iff_rank (A : Matrix m (Fin n) ℝ) (j : Fin n) :
    0 < descendingSingularValues A j ↔ j.val < A.rank := by
  rw [rank_eq_card_positive_descendingSingularValues]
  exact antitone_pos_iff_lt_card _ (descendingSingularValues_antitone A) j

theorem descendingSingularValues_eq_zero_iff_rank (A : Matrix m (Fin n) ℝ) (j : Fin n) :
    descendingSingularValues A j = 0 ↔ A.rank ≤ j.val := by
  rw [← not_lt, ← descendingSingularValues_pos_iff_rank]
  exact ⟨fun h => by rw [h]; exact lt_irrefl 0,
    fun h => le_antisymm (le_of_not_gt h) (descendingSingularValues_nonneg A j)⟩

end PaperI
