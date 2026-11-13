import PaperILean.DirectionalCoefficientJets

/-! The full polynomial differential of an affine vector field. The constant
coefficient of the output is retained here. No rank, nondegeneracy, or positive
degree assumption is used. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

def affineFieldPolynomialMap (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ where
  toFun P := ∑ i, affineCoordinate t N i * MvPolynomial.pderiv i P
  map_add' P Q := by
    simp only [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' a P := by
    simp only [Derivation.map_smul, mul_smul_comm, Finset.smul_sum, RingHom.id_apply]

theorem affineFieldPolynomialMap_apply (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    affineFieldPolynomialMap t N P =
      ∑ i, affineCoordinate t N i * MvPolynomial.pderiv i P := rfl

theorem affineFieldPolynomialMap_C (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) :
    affineFieldPolynomialMap t N (MvPolynomial.C c) = 0 := by
  simp [affineFieldPolynomialMap_apply]

theorem affineFieldPolynomialMap_add_C (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (P : MvPolynomial (Fin 3) ℝ) (c : ℝ) :
    affineFieldPolynomialMap t N (P + MvPolynomial.C c) =
      affineFieldPolynomialMap t N P := by
  rw [map_add, affineFieldPolynomialMap_C, add_zero]

theorem affineFieldPolynomialMap_sub_C (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (P : MvPolynomial (Fin 3) ℝ) (c : ℝ) :
    affineFieldPolynomialMap t N (P - MvPolynomial.C c) =
      affineFieldPolynomialMap t N P := by
  rw [map_sub, affineFieldPolynomialMap_C, sub_zero]

theorem affineFieldPolynomialMap_zero_field :
    affineFieldPolynomialMap 0 0 = 0 := by
  ext P e
  simp [affineFieldPolynomialMap_apply, affineCoordinate]

theorem affineFieldPolynomialMap_add_field (t u : PhysicalSpace)
    (N O : Matrix (Fin 3) (Fin 3) ℝ) :
    affineFieldPolynomialMap (t + u) (N + O) =
      affineFieldPolynomialMap t N + affineFieldPolynomialMap u O := by
  apply LinearMap.ext
  intro P
  simp only [LinearMap.add_apply, affineFieldPolynomialMap_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have h : affineCoordinate (t + u) (N + O) i =
      affineCoordinate t N i + affineCoordinate u O i := by
    simp [affineCoordinate, add_mul, Finset.sum_add_distrib]
    ring
  rw [h, add_mul]

theorem affineFieldPolynomialMap_smul_field (a : ℝ) (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) :
    affineFieldPolynomialMap (a • t) (a • N) = a • affineFieldPolynomialMap t N := by
  apply LinearMap.ext
  intro P
  simp only [LinearMap.smul_apply, affineFieldPolynomialMap_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h : affineCoordinate (a • t) (a • N) i = a • affineCoordinate t N i := by
    simp [affineCoordinate, smul_add, Finset.smul_sum, MvPolynomial.smul_eq_C_mul,
      map_mul, mul_assoc]
  rw [h, smul_mul_assoc]

theorem affineFieldPolynomialMap_translation (t : PhysicalSpace) :
    affineFieldPolynomialMap t 0 = directionalPolynomialMap t := by
  apply LinearMap.ext
  intro P
  rw [affineFieldPolynomialMap_apply, directionalPolynomialMap_apply]
  simp [affineCoordinate, directionalPolynomialPartial, MvPolynomial.smul_eq_C_mul]

theorem totalDegree_affineFieldPolynomialMap_le (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    (affineFieldPolynomialMap t N P).totalDegree ≤ P.totalDegree := by
  by_cases hzero : P.totalDegree = 0
  · rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero,
      affineFieldPolynomialMap_C]
    simp
  · rw [affineFieldPolynomialMap_apply]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    exact (MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add (affineCoordinate_degree t N i)
        (totalDegree_polynomialPartial_le i P)).trans (by omega))

theorem eval_affineFieldPolynomialMap (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (P : MvPolynomial (Fin 3) ℝ)
    (x : PhysicalSpace) :
    MvPolynomial.eval x (affineFieldPolynomialMap t N P) =
      fderiv ℝ (fun y : PhysicalSpace => MvPolynomial.eval y P) x (t + N *ᵥ x) := by
  rw [fderiv_evalPolynomial_apply, affineFieldPolynomialMap_apply]
  simp only [MvPolynomial.eval_sum, map_mul, eval_affineCoordinate]
  apply Finset.sum_congr rfl
  intro i hi
  simp [affinePoint, Matrix.mulVec, dotProduct, mul_comm]

theorem affineFieldPolynomialMap_X (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    affineFieldPolynomialMap t N (MvPolynomial.X j) = affineCoordinate t N j := by
  classical
  simp [affineFieldPolynomialMap_apply, MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]

theorem affineFieldPolynomialMap_mul (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (P Q : MvPolynomial (Fin 3) ℝ) :
    affineFieldPolynomialMap t N (P * Q) =
      affineFieldPolynomialMap t N P * Q + P * affineFieldPolynomialMap t N Q := by
  simp only [affineFieldPolynomialMap_apply, Derivation.leibniz, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem constantCoeff_affineFieldPolynomialMap (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.coeff 0 (affineFieldPolynomialMap t N P) =
      ∑ i, t i * MvPolynomial.coeff (Finsupp.single i 1) P := by
  change MvPolynomial.constantCoeff (affineFieldPolynomialMap t N P) = _
  rw [affineFieldPolynomialMap_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  change MvPolynomial.coeff 0 (affineCoordinate t N i) *
    MvPolynomial.coeff 0 (MvPolynomial.pderiv i P) = _
  rw [coeff_polynomialPartial]
  simp [affineCoordinate, MvPolynomial.coeff_sum]

theorem pderiv_affineCoordinate (p : PhysicalSpace)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    MvPolynomial.pderiv j (affineCoordinate p M i) = MvPolynomial.C (M i j) := by
  classical
  simp [affineCoordinate, MvPolynomial.pderiv_mul, Pi.single_apply, eq_comm]

theorem affineFieldPolynomialMap_shear (i j : Fin 3)
    (P : MvPolynomial (Fin 3) ℝ) :
    affineFieldPolynomialMap 0 (Matrix.stdBasisMatrix i j 1) P =
      MvPolynomial.X j * MvPolynomial.pderiv i P := by
  classical
  rw [affineFieldPolynomialMap_apply]
  have h (r : Fin 3) : affineCoordinate 0 (Matrix.stdBasisMatrix i j 1) r =
      if r = i then MvPolynomial.X j else 0 := by
    by_cases hr : r = i
    · subst r
      simp [affineCoordinate, Matrix.stdBasisMatrix, eq_comm]
    · simp [affineCoordinate, Matrix.stdBasisMatrix, hr, Ne.symm hr]
  simp [h]

theorem affineFieldPolynomialMap_affineCoordinate (t p : PhysicalSpace)
    (N M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    affineFieldPolynomialMap t N (affineCoordinate p M i) =
      affineCoordinate (M *ᵥ t) (M * N) i := by
  simp only [affineFieldPolynomialMap_apply, pderiv_affineCoordinate]
  simp only [affineCoordinate, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    map_sum, map_mul, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    ring

end PaperI
