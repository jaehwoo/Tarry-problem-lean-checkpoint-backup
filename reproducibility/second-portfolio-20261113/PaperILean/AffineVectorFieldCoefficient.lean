import PaperILean.AffineVectorFieldPolynomial

/-! The coefficient class `[XF]` of an affine vector field. The full polynomial
field action is formed before the constant term is removed. In particular,
linear-coordinate multipliers do not act on derivatives already reduced modulo
constants. No invertibility, rank, or positive-degree assumption is imposed.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

def affineFieldBoundedMap (k : ℕ) (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) :
    BoundedPolynomialSpace k →ₗ[ℝ] BoundedPolynomialSpace k where
  toFun P := ⟨affineFieldPolynomialMap t N P.val,
    (MvPolynomial.mem_restrictTotalDegree (Fin 3) k _).mpr
      ((totalDegree_affineFieldPolynomialMap_le t N P.val).trans
        ((MvPolynomial.mem_restrictTotalDegree (Fin 3) k P.val).mp P.property))⟩
  map_add' P Q := Subtype.ext ((affineFieldPolynomialMap t N).map_add P.val Q.val)
  map_smul' a P := Subtype.ext ((affineFieldPolynomialMap t N).map_smul a P.val)

def affineFieldCoefficientMap (k : ℕ) (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) :
    CoefficientSpace k →ₗ[ℝ] CoefficientSpace k :=
  (coefficientPolynomialEquiv k).symm.toLinearMap.comp
    ((discardConstant k).comp ((affineFieldBoundedMap k t N).comp
      (coefficientToBounded k)))

theorem polynomial_affineFieldCoefficientMap {k : ℕ} (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k) :
    coefficientPolynomial (affineFieldCoefficientMap k t N F) =
      affineFieldPolynomialMap t N (coefficientPolynomial F) -
        MvPolynomial.C (MvPolynomial.coeff 0
          (affineFieldPolynomialMap t N (coefficientPolynomial F))) := by
  change ((coefficientPolynomialEquiv k)
    ((coefficientPolynomialEquiv k).symm
      (discardConstant k (affineFieldBoundedMap k t N
        (coefficientToBounded k F))))).val = _
  rw [LinearEquiv.apply_symm_apply, discardConstant_eq]
  rfl

theorem coeff_affineFieldCoefficientMap {k : ℕ} (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k)
    (e : Fin 3 →₀ ℕ) (he : e ≠ 0) :
    MvPolynomial.coeff e (coefficientPolynomial (affineFieldCoefficientMap k t N F)) =
      MvPolynomial.coeff e (affineFieldPolynomialMap t N (coefficientPolynomial F)) := by
  rw [polynomial_affineFieldCoefficientMap, MvPolynomial.coeff_sub]
  simp only [MvPolynomial.coeff_C, if_neg (Ne.symm he), sub_zero]

theorem phase_affineFieldCoefficientMap {k : ℕ} (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k) (x : PhysicalSpace) :
    phase (affineFieldCoefficientMap k t N F) x =
      fderiv ℝ (phase F) x (t + N *ᵥ x) - fderiv ℝ (phase F) 0 t := by
  rw [← eval_coefficientPolynomial, polynomial_affineFieldCoefficientMap]
  simp only [map_sub, MvPolynomial.eval_C]
  change MvPolynomial.eval x (affineFieldPolynomialMap t N (coefficientPolynomial F)) -
    MvPolynomial.constantCoeff (affineFieldPolynomialMap t N (coefficientPolynomial F)) = _
  rw [← MvPolynomial.eval_zero, eval_affineFieldPolynomialMap,
    eval_affineFieldPolynomialMap]
  simp only [eval_coefficientPolynomial, Matrix.mulVec_zero, add_zero]

theorem affineFieldBoundedMap_add_field (k : ℕ) (t u : PhysicalSpace)
    (N M : Matrix (Fin 3) (Fin 3) ℝ) :
    affineFieldBoundedMap k (t + u) (N + M) =
      affineFieldBoundedMap k t N + affineFieldBoundedMap k u M := by
  ext1 P
  apply Subtype.ext
  exact congrArg (fun T : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ => T P.val)
    (affineFieldPolynomialMap_add_field t u N M)

theorem affineFieldBoundedMap_smul_field (k : ℕ) (a : ℝ) (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) :
    affineFieldBoundedMap k (a • t) (a • N) = a • affineFieldBoundedMap k t N := by
  ext1 P
  apply Subtype.ext
  exact congrArg (fun T : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ => T P.val)
    (affineFieldPolynomialMap_smul_field a t N)

theorem affineFieldBoundedMap_zero_field (k : ℕ) :
    affineFieldBoundedMap k 0 0 = 0 := by
  ext1 P
  apply Subtype.ext
  exact congrArg (fun T : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ => T P.val)
    affineFieldPolynomialMap_zero_field

theorem affineFieldBoundedMap_translation (k : ℕ) (t : PhysicalSpace) :
    affineFieldBoundedMap k t 0 = directionalBoundedMap k t := by
  ext1 P
  apply Subtype.ext
  exact congrArg (fun T : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ => T P.val)
    (affineFieldPolynomialMap_translation t)

theorem affineFieldCoefficientMap_add_field (k : ℕ) (t u : PhysicalSpace)
    (N M : Matrix (Fin 3) (Fin 3) ℝ) :
    affineFieldCoefficientMap k (t + u) (N + M) =
      affineFieldCoefficientMap k t N + affineFieldCoefficientMap k u M := by
  ext1 F
  change (coefficientPolynomialEquiv k).symm
    (discardConstant k (affineFieldBoundedMap k (t + u) (N + M) (coefficientToBounded k F))) = _
  rw [affineFieldBoundedMap_add_field]
  simp only [LinearMap.add_apply, map_add]
  rfl

theorem affineFieldCoefficientMap_smul_field (k : ℕ) (a : ℝ) (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) :
    affineFieldCoefficientMap k (a • t) (a • N) = a • affineFieldCoefficientMap k t N := by
  ext1 F
  change (coefficientPolynomialEquiv k).symm
    (discardConstant k (affineFieldBoundedMap k (a • t) (a • N) (coefficientToBounded k F))) = _
  rw [affineFieldBoundedMap_smul_field]
  simp only [LinearMap.smul_apply, map_smul]
  rfl

theorem affineFieldCoefficientMap_zero_field (k : ℕ) :
    affineFieldCoefficientMap k 0 0 = 0 := by
  ext1 F
  change (coefficientPolynomialEquiv k).symm
    (discardConstant k (affineFieldBoundedMap k 0 0 (coefficientToBounded k F))) = _
  rw [affineFieldBoundedMap_zero_field]
  simp only [LinearMap.zero_apply, map_zero]

theorem affineFieldCoefficientMap_translation (k : ℕ) (t : PhysicalSpace) :
    affineFieldCoefficientMap k t 0 = directionalCoefficientMap k t := by
  unfold affineFieldCoefficientMap directionalCoefficientMap
  rw [affineFieldBoundedMap_translation]

theorem affineFieldCoefficientMap_of_bounded (k : ℕ) (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (P : BoundedPolynomialSpace k) :
    affineFieldCoefficientMap k t N
      ((coefficientPolynomialEquiv k).symm (discardConstant k P)) =
        (coefficientPolynomialEquiv k).symm
          (discardConstant k (affineFieldBoundedMap k t N P)) := by
  have hrep : coefficientPolynomial
      ((coefficientPolynomialEquiv k).symm (discardConstant k P)) =
        P.val - MvPolynomial.C (MvPolynomial.coeff 0 P.val) := by
    change ((coefficientPolynomialEquiv k)
      ((coefficientPolynomialEquiv k).symm (discardConstant k P))).val = _
    rw [LinearEquiv.apply_symm_apply, discardConstant_eq]
  apply (coefficientPolynomialEquiv k).injective
  apply Subtype.ext
  change coefficientPolynomial (affineFieldCoefficientMap k t N
    ((coefficientPolynomialEquiv k).symm (discardConstant k P))) = _
  rw [polynomial_affineFieldCoefficientMap, hrep, affineFieldPolynomialMap_sub_C,
    LinearEquiv.apply_symm_apply, discardConstant_eq]
  rfl

theorem affineFieldCoefficientMap_degree_zero (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) : affineFieldCoefficientMap 0 t N = 0 := by
  ext F α
  exfalso
  have h := α.property
  omega

theorem exists_coefficientPolynomial_X {k : ℕ} (hk : 1 ≤ k) (i : Fin 3) :
    ∃ F : CoefficientSpace k, coefficientPolynomial F = MvPolynomial.X i := by
  have hX : (MvPolynomial.X i : MvPolynomial (Fin 3) ℝ) ∈
      zeroConstantPolynomialSpace k := by
    rw [mem_zeroConstantPolynomialSpace]
    exact ⟨by simpa using hk, by simp⟩
  refine ⟨(coefficientPolynomialEquiv k).symm ⟨MvPolynomial.X i, hX⟩, ?_⟩
  exact congrArg (fun P : zeroConstantPolynomialSpace k => P.val)
    ((coefficientPolynomialEquiv k).apply_symm_apply _)

theorem directionalCoefficientMap_of_polynomial_X {k : ℕ} (u : PhysicalSpace)
    (i : Fin 3) (F : CoefficientSpace k) (hF : coefficientPolynomial F = MvPolynomial.X i) :
    directionalCoefficientMap k u F = 0 := by
  apply (coefficientPolynomialEquiv k).injective
  apply Subtype.ext
  change coefficientPolynomial (directionalCoefficientMap k u F) = _
  rw [polynomial_directionalCoefficientMap, hF]
  have h : directionalPolynomialPartial u (MvPolynomial.X i) = MvPolynomial.C (u i) := by
    simp [directionalPolynomialPartial, MvPolynomial.pderiv_X, MvPolynomial.smul_eq_C_mul, Pi.single_apply]
  simp [h]


theorem polynomial_affineFieldCoefficientMap_of_polynomial_X {k : ℕ}
    (t : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3)
    (F : CoefficientSpace k) (hF : coefficientPolynomial F = MvPolynomial.X i) :
    coefficientPolynomial (affineFieldCoefficientMap k t N F) =
      ∑ j : Fin 3, MvPolynomial.C (N i j) * MvPolynomial.X j := by
  rw [polynomial_affineFieldCoefficientMap, hF, affineFieldPolynomialMap_X]
  simp [affineCoordinate, MvPolynomial.coeff_sum]

theorem exists_affineFieldCoefficient_derivative_constant_obstruction {k : ℕ}
    (hk : 1 ≤ k) :
    ∃ F : CoefficientSpace k,
      coefficientPolynomial F = MvPolynomial.X 0 ∧
      (∀ u : PhysicalSpace, directionalCoefficientMap k u F = 0) ∧
      coefficientPolynomial
        (affineFieldCoefficientMap k 0
          (fun i j : Fin 3 => if i = 0 ∧ j = 1 then (1 : ℝ) else 0) F) =
        MvPolynomial.X 1 := by
  obtain ⟨F, hF⟩ := exists_coefficientPolynomial_X hk (0 : Fin 3)
  refine ⟨F, hF, fun u => directionalCoefficientMap_of_polynomial_X u 0 F hF, ?_⟩
  rw [polynomial_affineFieldCoefficientMap_of_polynomial_X 0 _ 0 F hF]
  simp

end PaperI
