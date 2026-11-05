import PaperILean.MiddleSingularNorm
import PaperILean.OrderedSingularBasis

/-! The actual two-dimensional min--max argument at I3253. A nonzero
combination of the first two right singular vectors of M has image orthogonal
to the last right singular vector of B. The saved singular-basis inequalities
then give the middle-singular-value bound in the literal Euclidean norms. -/

noncomputable section
open scoped Matrix InnerProductSpace
namespace PaperI.MiddleSingularMinMax
open MiddleSingularNorm

theorem exists_top_pair_orthogonal_image
    (B : Matrix (Fin 3) (Fin 3) ℝ) (M : Matrix (Fin 3) (Fin 4) ℝ) :
    ∃ x : EuclideanSpace ℝ (Fin 4), x ≠ 0 ∧
      (∀ j : Fin 4, (1 : Fin 4) < j → ⟪orderedSingularBasis M j, x⟫_ℝ = 0) ∧
      (∀ j : Fin 3, (1 : Fin 3) < j →
        ⟪orderedSingularBasis B j, Matrix.toEuclideanLin M x⟫_ℝ = 0) := by
  let e := orderedSingularBasis M
  let f := orderedSingularBasis B
  let p : ℝ := ⟪f 2, Matrix.toEuclideanLin M (e 0)⟫_ℝ
  let q : ℝ := ⟪f 2, Matrix.toEuclideanLin M (e 1)⟫_ℝ
  by_cases hp : p = 0
  · refine ⟨e 0, ?_, ?_, ?_⟩
    · intro hz
      have hn := e.norm_eq_one (0 : Fin 4)
      rw [hz, norm_zero] at hn
      norm_num at hn
    · intro j hj
      exact e.inner_eq_zero (by omega : j ≠ 0)
    · intro j hj
      have hj2 : j = 2 := by apply Fin.ext; omega
      subst j
      exact hp
  · let x := q • e 0 - p • e 1
    have hx1 : ⟪e 1, x⟫_ℝ = -p := by
      dsimp only [x]
      rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
        e.inner_eq_zero (by decide : (1 : Fin 4) ≠ 0),
        real_inner_self_eq_norm_sq, e.norm_eq_one]
      ring
    refine ⟨x, ?_, ?_, ?_⟩
    · intro hz
      rw [hz, inner_zero_right] at hx1
      exact hp (by linarith)
    · intro j hj
      change ⟪e j, q • e 0 - p • e 1⟫_ℝ = 0
      rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
        e.inner_eq_zero (by omega : j ≠ 0), e.inner_eq_zero (by omega : j ≠ 1)]
      ring
    · intro j hj
      have hj2 : j = 2 := by apply Fin.ext; omega
      subst j
      change ⟪f 2, Matrix.toEuclideanLin M (q • e 0 - p • e 1)⟫_ℝ = 0
      rw [map_sub, map_smul, map_smul, inner_sub_right,
        real_inner_smul_right, real_inner_smul_right]
      change q * p - p * q = 0
      ring

/-- Literal middle-singular-value product inequality for a 3-by-3 physical
matrix and the actual 3-by-4 affine-field matrix. Degenerate matrices are allowed. -/
theorem middle_singular_mul_le_frobenius
    (B : Matrix (Fin 3) (Fin 3) ℝ) (M : Matrix (Fin 3) (Fin 4) ℝ) :
    descendingSingularValues B (1 : Fin 3) *
      descendingSingularValues M (1 : Fin 4) ≤ matrixFrobenius (B * M) := by
  obtain ⟨x, hx, hxM, hxB⟩ := exists_top_pair_orthogonal_image B M
  have hM := ordered_singular_lower_bound_of_tail_zero M (1 : Fin 4) x hxM
  have hB := ordered_singular_lower_bound_of_tail_zero B (1 : Fin 3)
    (Matrix.toEuclideanLin M x) hxB
  have hprod : (descendingSingularValues B (1 : Fin 3) *
      descendingSingularValues M (1 : Fin 4)) * ‖x‖ ≤ matrixFrobenius (B * M) * ‖x‖ := by
    calc
      (descendingSingularValues B (1 : Fin 3) *
          descendingSingularValues M (1 : Fin 4)) * ‖x‖ =
        descendingSingularValues B (1 : Fin 3) *
          (descendingSingularValues M (1 : Fin 4) * ‖x‖) := by ring
      _ ≤ descendingSingularValues B (1 : Fin 3) * ‖Matrix.toEuclideanLin M x‖ :=
        mul_le_mul_of_nonneg_left hM (descendingSingularValues_nonneg _ _)
      _ ≤ ‖Matrix.toEuclideanLin B (Matrix.toEuclideanLin M x)‖ := hB
      _ = ‖Matrix.toEuclideanLin (B * M) x‖ := by rw [toEuclideanLin_mul_apply]
      _ ≤ matrixFrobenius (B * M) * ‖x‖ := euclidean_mul_norm_le_frobenius _ _
  exact (mul_le_mul_right (norm_pos_iff.mpr hx)).mp hprod

end PaperI.MiddleSingularMinMax
