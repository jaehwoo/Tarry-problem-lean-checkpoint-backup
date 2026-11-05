import PaperILean.OriginalGaussCoefficientPerturbation

/-! Complete original coefficient samples under separate bounded right affine
changes. Every nonconstant coefficient and every translation is retained.
The comparison constant is independent of the number of sample blocks. -/

noncomputable section
open scoped BigOperators

namespace PaperI.OriginalSamplingComparisons

def completeSampleMap (k m : ℕ) (h : Fin m → (Fin 6 → ℝ)) :
    CoefficientSpace k →ₗ[ℝ] ((Fin m × MonomialIndex k) → ℝ) where
  toFun J p := originalUpperCoefficientPullback J (h p.1) p.2
  map_add' J K := by
    funext p
    exact congrFun (map_add
      (affineCoefficientMap k ![h p.1 2, h p.1 4, h p.1 5]
        (originalUpperLinearMatrix (h p.1))) J K) p.2
  map_smul' c J := by
    funext p
    exact congrFun (map_smul
      (affineCoefficientMap k ![h p.1 2, h p.1 4, h p.1 5]
        (originalUpperLinearMatrix (h p.1))) c J) p.2

theorem completeSampleMap_apply (k m : ℕ) (h : Fin m → (Fin 6 → ℝ))
    (J : CoefficientSpace k) (i : Fin m) (α : MonomialIndex k) :
    completeSampleMap k m h J (i, α) =
      originalUpperCoefficientPullback J (h i) α := rfl

def RightClose {m : ℕ} (T : ℝ) (h q : Fin m → (Fin 6 → ℝ)) : Prop :=
  ∃ u : Fin m → (Fin 6 → ℝ),
    (∀ i, h i = originalUpperAffineComp (q i) (u i)) ∧
    (∀ i, ‖u i‖ ≤ T) ∧
    (∀ i, ‖originalUpperAffineInv (u i)‖ ≤ T)

theorem completeSampleMap_sq (k m : ℕ) (h : Fin m → (Fin 6 → ℝ))
    (J : CoefficientSpace k) :
    coordinateL2Norm (completeSampleMap k m h J) ^ 2 =
      ∑ i, coefficientEuclideanNorm (originalUpperCoefficientPullback J (h i)) ^ 2 := by
  rw [coordinateL2Norm_sq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact (coordinateL2Norm_sq (originalUpperCoefficientPullback J (h i))).symm

theorem completeSampleMap_le_of_block_bounds (k m : ℕ)
    (h q : Fin m → (Fin 6 → ℝ)) (J : CoefficientSpace k) (A : ℝ)
    (hA : 0 ≤ A)
    (hb : ∀ i, coefficientEuclideanNorm (originalUpperCoefficientPullback J (h i)) ≤
      A * coefficientEuclideanNorm (originalUpperCoefficientPullback J (q i))) :
    coordinateL2Norm (completeSampleMap k m h J) ≤
      A * coordinateL2Norm (completeSampleMap k m q J) := by
  have hs : coordinateL2Norm (completeSampleMap k m h J) ^ 2 ≤
      (A * coordinateL2Norm (completeSampleMap k m q J)) ^ 2 := by
    rw [mul_pow, completeSampleMap_sq, completeSampleMap_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hn : 0 ≤ coefficientEuclideanNorm
        (originalUpperCoefficientPullback J (h i)) := Real.sqrt_nonneg _
    have hn' : 0 ≤ coefficientEuclideanNorm
        (originalUpperCoefficientPullback J (q i)) := Real.sqrt_nonneg _
    have ht := mul_self_le_mul_self hn (hb i)
    nlinarith
  have hn := coordinateL2Norm_nonneg (completeSampleMap k m h J)
  have hn' := coordinateL2Norm_nonneg (completeSampleMap k m q J)
  nlinarith [mul_nonneg hA hn']

theorem completeSampleMap_rightClose_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      ∀ (h q : Fin m → (Fin 6 → ℝ)), RightClose T h q →
      ∀ J : CoefficientSpace k,
        coordinateL2Norm (completeSampleMap k m h J) ≤
          C * (3 * (1 + T)) ^ (2 * k) *
            coordinateL2Norm (completeSampleMap k m q J) ∧
        coordinateL2Norm (completeSampleMap k m q J) ≤
          C * (3 * (1 + T)) ^ (2 * k) *
            coordinateL2Norm (completeSampleMap k m h J) := by
  obtain ⟨C, hC, hbound⟩ := originalUpperCoefficient_polynomial_bound k
  refine ⟨C, hC, ?_⟩
  intro m T hT h q hclose J
  obtain ⟨u, hu, huT, huinvT⟩ := hclose
  have hA : 0 ≤ C * (3 * (1 + T)) ^ (2 * k) := by positivity
  constructor
  · apply completeSampleMap_le_of_block_bounds k m h q J _ hA
    intro i
    have hb := hbound T hT (originalUpperCoefficientPullback J (q i)) (u i) (huT i)
    rw [originalUpperCoefficientPullback_comp, ← hu i] at hb
    exact hb
  · apply completeSampleMap_le_of_block_bounds k m q h J _ hA
    intro i
    have hb := hbound T hT (originalUpperCoefficientPullback J (h i))
      (originalUpperAffineInv (u i)) (huinvT i)
    have hid : originalUpperAffineComp (q i) 0 = q i := by
      funext a
      fin_cases a <;> simp [originalUpperAffineComp]
    have hframe : originalUpperAffineComp (h i) (originalUpperAffineInv (u i)) = q i := by
      rw [hu i, originalUpperAffineComp_assoc, (originalUpperAffineComp_inv (u i)).2, hid]
    rw [originalUpperCoefficientPullback_comp, hframe] at hb
    exact hb

end PaperI.OriginalSamplingComparisons
