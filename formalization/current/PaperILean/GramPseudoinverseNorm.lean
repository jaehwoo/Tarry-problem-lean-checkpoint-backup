import PaperILean.RegularSectionPseudoinverse
import PaperILean.TensorContractionBounds

/-! The quantitative estimate for the literal Gram left pseudoinverse used
in I1448[42,78) and I1450[0,88). All vector norms are the actual Euclidean
coordinate norms. The estimate is generic in the rectangular matrix, so it
applies to every omitted orbit column, not only the D complement. -/

noncomputable section
open scoped BigOperators Matrix

namespace PaperI.GramPseudoinverseNorm

open RegularSectionPseudoinverse

/-- The literal Gram pseudoinverse has Euclidean norm at most the reciprocal
of any positive lower bound for the least singular value. -/
theorem leftPseudoinverse_mulVec_norm_le
    {m : Type*} [Fintype m] {n : ℕ}
    (L : Matrix m (Fin (n + 1)) ℝ)
    (τ : ℝ) (hτ : 0 < τ)
    (hL : τ ≤ descendingSingularValues L (Fin.last n))
    (y : m → ℝ) :
    coordinateL2Norm (leftPseudoinverse L *ᵥ y) ≤
      τ⁻¹ * coordinateL2Norm y := by
  classical
  let x := leftPseudoinverse L *ᵥ y
  let z := L *ᵥ x
  have hleft := leftPseudoinverse_mul_of_singular_lower L τ hτ hL
  have hgi : (L.transpose * L)⁻¹ * (L.transpose * L) = 1 := by
    simpa only [leftPseudoinverse, Matrix.mul_assoc] using hleft
  have hig : (L.transpose * L) * (L.transpose * L)⁻¹ = 1 :=
    Matrix.mul_eq_one_comm.mp hgi
  have hnormalMatrix : (L.transpose * L) * leftPseudoinverse L = L.transpose := by
    unfold leftPseudoinverse
    rw [← Matrix.mul_assoc, hig, Matrix.one_mul]
  have hnormal : L.transpose *ᵥ z = L.transpose *ᵥ y := by
    dsimp only [z, x]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hnormalMatrix]
  have hdot : dotProduct z z = dotProduct z y := by
    calc
      dotProduct z z = dotProduct x (L.transpose *ᵥ z) := by
        have h := Matrix.dotProduct_mulVec x L.transpose z
        rw [Matrix.vecMul_transpose] at h
        exact h.symm
      _ = dotProduct x (L.transpose *ᵥ y) := by rw [hnormal]
      _ = dotProduct z y := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hcs : |dotProduct z y| ≤ coordinateL2Norm z * coordinateL2Norm y := by
    apply (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (coordinateL2Norm_nonneg z) (coordinateL2Norm_nonneg y))).mp
    simpa only [sq_abs, dotProduct, mul_pow, coordinateL2Norm_sq] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ z y
  have hsq : coordinateL2Norm z ^ 2 ≤ coordinateL2Norm z * coordinateL2Norm y := by
    calc
      coordinateL2Norm z ^ 2 = dotProduct z z := by
        rw [coordinateL2Norm_sq]
        simp only [dotProduct, pow_two]
      _ = dotProduct z y := hdot
      _ ≤ |dotProduct z y| := le_abs_self _
      _ ≤ coordinateL2Norm z * coordinateL2Norm y := hcs
  have hz : coordinateL2Norm z ≤ coordinateL2Norm y := by
    by_cases he : coordinateL2Norm z = 0
    · simpa only [he] using coordinateL2Norm_nonneg y
    · have hp : 0 < coordinateL2Norm z :=
        lt_of_le_of_ne (coordinateL2Norm_nonneg z) (Ne.symm he)
      exact (mul_le_mul_left hp).mp (by simpa only [pow_two] using hsq)
  have hlow := (le_least_descendingSingularValue_iff L τ).mp hL
    ((WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm x)
  have hlow' : τ * coordinateL2Norm x ≤ coordinateL2Norm z := by
    simpa only [coordinateL2Norm_eq_norm,
      Matrix.toEuclideanLin_apply_piLp_equiv_symm, z] using hlow
  have h := mul_le_mul_of_nonneg_left (hlow'.trans hz) (inv_nonneg.mpr hτ.le)
  change coordinateL2Norm x ≤ τ⁻¹ * coordinateL2Norm y
  simpa only [← mul_assoc, inv_mul_cancel₀ hτ.ne', one_mul] using h

end PaperI.GramPseudoinverseNorm
