import PaperILean.PolynomialQuotient
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Fixed affine pullback on the complete parent coefficient space.
The degree estimate also holds for singular matrices; invertibility is not
assumed until an inverse is constructed. No determinant formula is asserted. -/

open scoped BigOperators
open Matrix

noncomputable section
namespace PaperI

def affinePoint (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (x : PhysicalSpace) : PhysicalSpace :=
  fun i => c i + ∑ j, B i j * x j

def affineCoordinate (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (i : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C (c i) + ∑ j, MvPolynomial.C (B i j) * MvPolynomial.X j

theorem affineCoordinate_degree (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (i : Fin 3) : (affineCoordinate c B i).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C (B i j))
      (MvPolynomial.X j : MvPolynomial (Fin 3) ℝ)

theorem linearSubstitution_degree (g : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (P : MvPolynomial (Fin 3) ℝ) :
    (MvPolynomial.aeval g P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  rw [MvPolynomial.aeval_monomial]
  change (MvPolynomial.C (MvPolynomial.coeff e P) *
    e.prod (fun i n => g i ^ n)).totalDegree ≤ P.totalDegree
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
  apply (MvPolynomial.totalDegree_finset_prod _ _).trans
  calc
    ∑ i, (g i ^ e i).totalDegree ≤ ∑ i, e i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (MvPolynomial.totalDegree_pow _ _).trans
        (by simpa using Nat.mul_le_mul_left (e i) (hg i))
    _ = e.sum (fun _ n => n) := by
      rw [Finsupp.sum_fintype _ _ (by intro i; rfl)]
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree he

def affinePolynomialMap (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval (affineCoordinate c B)

theorem affinePolynomialMap_degree (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (P : MvPolynomial (Fin 3) ℝ) :
    (affinePolynomialMap c B P).totalDegree ≤ P.totalDegree :=
  linearSubstitution_degree _ (affineCoordinate_degree c B) P

theorem eval_affineCoordinate (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (x : PhysicalSpace) (i : Fin 3) :
    MvPolynomial.eval x (affineCoordinate c B i) = affinePoint c B x i := by
  simp [affineCoordinate, affinePoint, MvPolynomial.eval_sum]

theorem eval_affinePolynomialMap (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (P : MvPolynomial (Fin 3) ℝ) (x : PhysicalSpace) :
    MvPolynomial.eval x (affinePolynomialMap c B P) =
      MvPolynomial.eval (affinePoint c B x) P := by
  change MvPolynomial.aeval x (MvPolynomial.aeval (affineCoordinate c B) P) = _
  rw [MvPolynomial.comp_aeval_apply]
  have hg : (fun i => MvPolynomial.aeval x (affineCoordinate c B i)) =
      affinePoint c B x := by
    funext i
    exact eval_affineCoordinate c B x i
  rw [hg]
  rfl

def affineBoundedMap (k : ℕ) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    BoundedPolynomialSpace k →ₗ[ℝ] BoundedPolynomialSpace k :=
  { toFun := fun P => ⟨affinePolynomialMap c B P.val,
      (MvPolynomial.mem_restrictTotalDegree (Fin 3) k _).mpr
        ((affinePolynomialMap_degree c B P.val).trans
          ((MvPolynomial.mem_restrictTotalDegree (Fin 3) k P.val).mp P.property))⟩
    map_add' := by intro P Q; apply Subtype.ext; exact map_add _ _ _
    map_smul' := by intro a P; apply Subtype.ext; exact map_smul _ _ _ }

def coefficientToBounded (k : ℕ) : CoefficientSpace k →ₗ[ℝ] BoundedPolynomialSpace k :=
  { toFun := fun F => ⟨coefficientPolynomial F,
      (MvPolynomial.mem_restrictTotalDegree (Fin 3) k _).mpr
        (coefficientPolynomial_totalDegree F)⟩
    map_add' := by
      intro F G
      apply Subtype.ext
      change coefficientPolynomial (F + G) = coefficientPolynomial F + coefficientPolynomial G
      exact congrArg (fun P : zeroConstantPolynomialSpace k => P.val)
        ((coefficientPolynomialEquiv k).map_add F G)
    map_smul' := by
      intro a F
      apply Subtype.ext
      change coefficientPolynomial (a • F) = a • coefficientPolynomial F
      exact congrArg (fun P : zeroConstantPolynomialSpace k => P.val)
        ((coefficientPolynomialEquiv k).map_smul a F) }

def affineCoefficientMap (k : ℕ) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    CoefficientSpace k →ₗ[ℝ] CoefficientSpace k :=
  ((coefficientPolynomialEquiv k).symm.toLinearMap).comp
    ((discardConstant k).comp ((affineBoundedMap k c B).comp (coefficientToBounded k)))

theorem polynomial_affineCoefficientMap (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k) :
    coefficientPolynomial (affineCoefficientMap k c B F) =
      affinePolynomialMap c B (coefficientPolynomial F) -
        MvPolynomial.C (phase F c) := by
  have h := congrArg Subtype.val ((coefficientPolynomialEquiv k).apply_symm_apply
    (discardConstant k (affineBoundedMap k c B (coefficientToBounded k F))))
  change coefficientPolynomial (affineCoefficientMap k c B F) =
    (discardConstant k (affineBoundedMap k c B (coefficientToBounded k F))).val at h
  rw [h, discardConstant_eq]
  change affinePolynomialMap c B (coefficientPolynomial F) -
    MvPolynomial.C (MvPolynomial.coeff 0 (affinePolynomialMap c B
      (coefficientPolynomial F))) = _
  have hz : MvPolynomial.coeff 0 (affinePolynomialMap c B (coefficientPolynomial F)) =
      phase F c := by
    change MvPolynomial.constantCoeff (affinePolynomialMap c B (coefficientPolynomial F)) = _
    rw [← MvPolynomial.eval_zero]
    rw [eval_affinePolynomialMap]
    have hp : affinePoint c B (0 : PhysicalSpace) = c := by
      funext i
      simp [affinePoint]
    rw [hp, eval_coefficientPolynomial]
  rw [hz]

theorem phase_affineCoefficientMap (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k) (x : PhysicalSpace) :
    phase (affineCoefficientMap k c B F) x = phase F (affinePoint c B x) - phase F c := by
  rw [← eval_coefficientPolynomial, polynomial_affineCoefficientMap,
    map_sub, MvPolynomial.eval_C, eval_affinePolynomialMap, eval_coefficientPolynomial]

theorem coefficient_ext {k : ℕ} (F G : CoefficientSpace k)
    (h : ∀ x : PhysicalSpace, phase F x = phase G x) : F = G := by
  apply (coefficientPolynomialEquiv k).injective
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.eval x (coefficientPolynomial F) =
    MvPolynomial.eval x (coefficientPolynomial G)
  simpa only [eval_coefficientPolynomial] using h x

theorem phase_zero {k : ℕ} (F : CoefficientSpace k) : phase F 0 = 0 := by
  rw [← eval_coefficientPolynomial, MvPolynomial.eval_zero]
  exact coefficientPolynomial_constantCoeff F

theorem affinePoint_comp (c d : PhysicalSpace)
    (B A : Matrix (Fin 3) (Fin 3) ℝ) (x : PhysicalSpace) :
    affinePoint c B (affinePoint d A x) = affinePoint (c + B *ᵥ d) (B * A) x := by
  change c + B *ᵥ (d + A *ᵥ x) = (c + B *ᵥ d) + (B * A) *ᵥ x
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]

theorem affineCoefficientMap_comp (k : ℕ) (c d : PhysicalSpace)
    (B A : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k) :
    affineCoefficientMap k d A (affineCoefficientMap k c B F) =
      affineCoefficientMap k (c + B *ᵥ d) (B * A) F := by
  apply coefficient_ext
  intro x
  rw [phase_affineCoefficientMap, phase_affineCoefficientMap,
    phase_affineCoefficientMap, phase_affineCoefficientMap, affinePoint_comp]
  change (phase F (affinePoint (c + B *ᵥ d) (B * A) x) - phase F c) -
    (phase F (c + B *ᵥ d) - phase F c) = _
  ring

theorem affineCoefficientMap_identity (k : ℕ) (F : CoefficientSpace k) :
    affineCoefficientMap k 0 (1 : Matrix (Fin 3) (Fin 3) ℝ) F = F := by
  apply coefficient_ext
  intro x
  rw [phase_affineCoefficientMap, phase_zero, sub_zero]
  have hx : affinePoint 0 (1 : Matrix (Fin 3) (Fin 3) ℝ) x = x := by
    change 0 + (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x = x
    simp
  rw [hx]

theorem affineCoefficientMap_inverse_left (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) (F : CoefficientSpace k) :
    affineCoefficientMap k (-(B⁻¹ *ᵥ c)) B⁻¹ (affineCoefficientMap k c B F) = F := by
  rw [affineCoefficientMap_comp, B.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hB)]
  have hc : c + B *ᵥ (-(B⁻¹ *ᵥ c)) = 0 := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      B.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec]
    exact add_neg_cancel c
  rw [hc, affineCoefficientMap_identity]

theorem affineCoefficientMap_inverse_right (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) (F : CoefficientSpace k) :
    affineCoefficientMap k c B (affineCoefficientMap k (-(B⁻¹ *ᵥ c)) B⁻¹ F) = F := by
  rw [affineCoefficientMap_comp, B.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hB)]
  rw [neg_add_cancel, affineCoefficientMap_identity]

def affineCoefficientEquiv (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) :
    CoefficientSpace k ≃ₗ[ℝ] CoefficientSpace k :=
  { affineCoefficientMap k c B with
    invFun := affineCoefficientMap k (-(B⁻¹ *ᵥ c)) B⁻¹
    left_inv := affineCoefficientMap_inverse_left k c B hB
    right_inv := affineCoefficientMap_inverse_right k c B hB }

end PaperI
