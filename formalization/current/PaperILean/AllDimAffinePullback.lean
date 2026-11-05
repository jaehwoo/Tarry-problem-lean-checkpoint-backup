import PaperILean.AllDimPolynomialQuotient
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Fixed affine pullback on the complete parent coefficient space.
The degree estimate also holds for singular matrices; invertibility is not
assumed until an inverse is constructed. No determinant formula is asserted. -/

open scoped BigOperators
open Matrix

noncomputable section
namespace PaperI.AllDim

variable {n : ℕ}

def affinePoint (c : (PhysicalSpace n)) (B : Matrix (Fin n) (Fin n) ℝ)
    (x : (PhysicalSpace n)) : (PhysicalSpace n) :=
  fun i => c i + ∑ j, B i j * x j

def affineCoordinate (c : (PhysicalSpace n)) (B : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (c i) + ∑ j, MvPolynomial.C (B i j) * MvPolynomial.X j

theorem affineCoordinate_degree (c : (PhysicalSpace n)) (B : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : (affineCoordinate c B i).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C (B i j))
      (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)

theorem linearSubstitution_degree (g : Fin n → MvPolynomial (Fin n) ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (P : MvPolynomial (Fin n) ℝ) :
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

def affinePolynomialMap (c : (PhysicalSpace n)) (B : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  MvPolynomial.aeval (affineCoordinate c B)

theorem affinePolynomialMap_degree (c : (PhysicalSpace n)) (B : Matrix (Fin n) (Fin n) ℝ)
    (P : MvPolynomial (Fin n) ℝ) :
    (affinePolynomialMap c B P).totalDegree ≤ P.totalDegree :=
  linearSubstitution_degree _ (affineCoordinate_degree c B) P

theorem eval_affineCoordinate (c : (PhysicalSpace n)) (B : Matrix (Fin n) (Fin n) ℝ)
    (x : (PhysicalSpace n)) (i : Fin n) :
    MvPolynomial.eval x (affineCoordinate c B i) = affinePoint c B x i := by
  simp [affineCoordinate, affinePoint, MvPolynomial.eval_sum]

theorem eval_affinePolynomialMap (c : (PhysicalSpace n)) (B : Matrix (Fin n) (Fin n) ℝ)
    (P : MvPolynomial (Fin n) ℝ) (x : (PhysicalSpace n)) :
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

def affineBoundedMap (n k : ℕ) (c : (PhysicalSpace n)) (B : Matrix (Fin n) (Fin n) ℝ) :
    BoundedPolynomialSpace n k →ₗ[ℝ] BoundedPolynomialSpace n k :=
  { toFun := fun P => ⟨affinePolynomialMap c B P.val,
      (MvPolynomial.mem_restrictTotalDegree (Fin n) k _).mpr
        ((affinePolynomialMap_degree c B P.val).trans
          ((MvPolynomial.mem_restrictTotalDegree (Fin n) k P.val).mp P.property))⟩
    map_add' := by intro P Q; apply Subtype.ext; exact map_add _ _ _
    map_smul' := by intro a P; apply Subtype.ext; exact map_smul _ _ _ }

def coefficientToBounded (n k : ℕ) : CoefficientSpace n k →ₗ[ℝ] BoundedPolynomialSpace n k :=
  { toFun := fun F => ⟨coefficientPolynomial F,
      (MvPolynomial.mem_restrictTotalDegree (Fin n) k _).mpr
        (coefficientPolynomial_totalDegree F)⟩
    map_add' := by
      intro F G
      apply Subtype.ext
      change coefficientPolynomial (F + G) = coefficientPolynomial F + coefficientPolynomial G
      exact congrArg (fun P : zeroConstantPolynomialSpace n k => P.val)
        ((coefficientPolynomialEquiv n k).map_add F G)
    map_smul' := by
      intro a F
      apply Subtype.ext
      change coefficientPolynomial (a • F) = a • coefficientPolynomial F
      exact congrArg (fun P : zeroConstantPolynomialSpace n k => P.val)
        ((coefficientPolynomialEquiv n k).map_smul a F) }

def affineCoefficientMap (n k : ℕ) (c : (PhysicalSpace n)) (B : Matrix (Fin n) (Fin n) ℝ) :
    CoefficientSpace n k →ₗ[ℝ] CoefficientSpace n k :=
  ((coefficientPolynomialEquiv n k).symm.toLinearMap).comp
    ((discardConstant n k).comp ((affineBoundedMap n k c B).comp (coefficientToBounded n k)))

theorem polynomial_affineCoefficientMap (n k : ℕ) (c : (PhysicalSpace n))
    (B : Matrix (Fin n) (Fin n) ℝ) (F : CoefficientSpace n k) :
    coefficientPolynomial (affineCoefficientMap n k c B F) =
      affinePolynomialMap c B (coefficientPolynomial F) -
        MvPolynomial.C (phase F c) := by
  have h := congrArg Subtype.val ((coefficientPolynomialEquiv n k).apply_symm_apply
    (discardConstant n k (affineBoundedMap n k c B (coefficientToBounded n k F))))
  change coefficientPolynomial (affineCoefficientMap n k c B F) =
    (discardConstant n k (affineBoundedMap n k c B (coefficientToBounded n k F))).val at h
  rw [h, discardConstant_eq]
  change affinePolynomialMap c B (coefficientPolynomial F) -
    MvPolynomial.C (MvPolynomial.coeff 0 (affinePolynomialMap c B
      (coefficientPolynomial F))) = _
  have hz : MvPolynomial.coeff 0 (affinePolynomialMap c B (coefficientPolynomial F)) =
      phase F c := by
    change MvPolynomial.constantCoeff (affinePolynomialMap c B (coefficientPolynomial F)) = _
    rw [← MvPolynomial.eval_zero]
    rw [eval_affinePolynomialMap]
    have hp : affinePoint c B (0 : (PhysicalSpace n)) = c := by
      funext i
      simp [affinePoint]
    rw [hp, eval_coefficientPolynomial]
  rw [hz]

theorem phase_affineCoefficientMap (n k : ℕ) (c : (PhysicalSpace n))
    (B : Matrix (Fin n) (Fin n) ℝ) (F : CoefficientSpace n k) (x : (PhysicalSpace n)) :
    phase (affineCoefficientMap n k c B F) x = phase F (affinePoint c B x) - phase F c := by
  rw [← eval_coefficientPolynomial, polynomial_affineCoefficientMap,
    map_sub, MvPolynomial.eval_C, eval_affinePolynomialMap, eval_coefficientPolynomial]

theorem coefficient_ext {n k : ℕ} (F G : CoefficientSpace n k)
    (h : ∀ x : (PhysicalSpace n), phase F x = phase G x) : F = G := by
  apply (coefficientPolynomialEquiv n k).injective
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.eval x (coefficientPolynomial F) =
    MvPolynomial.eval x (coefficientPolynomial G)
  simpa only [eval_coefficientPolynomial] using h x

theorem phase_zero {n k : ℕ} (F : CoefficientSpace n k) : phase F 0 = 0 := by
  rw [← eval_coefficientPolynomial, MvPolynomial.eval_zero]
  exact coefficientPolynomial_constantCoeff F

theorem affinePoint_comp (c d : (PhysicalSpace n))
    (B A : Matrix (Fin n) (Fin n) ℝ) (x : (PhysicalSpace n)) :
    affinePoint c B (affinePoint d A x) = affinePoint (c + B *ᵥ d) (B * A) x := by
  change c + B *ᵥ (d + A *ᵥ x) = (c + B *ᵥ d) + (B * A) *ᵥ x
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]

theorem affineCoefficientMap_comp (n k : ℕ) (c d : (PhysicalSpace n))
    (B A : Matrix (Fin n) (Fin n) ℝ) (F : CoefficientSpace n k) :
    affineCoefficientMap n k d A (affineCoefficientMap n k c B F) =
      affineCoefficientMap n k (c + B *ᵥ d) (B * A) F := by
  apply coefficient_ext
  intro x
  rw [phase_affineCoefficientMap, phase_affineCoefficientMap,
    phase_affineCoefficientMap, phase_affineCoefficientMap, affinePoint_comp]
  change (phase F (affinePoint (c + B *ᵥ d) (B * A) x) - phase F c) -
    (phase F (c + B *ᵥ d) - phase F c) = _
  ring

theorem affineCoefficientMap_identity (n k : ℕ) (F : CoefficientSpace n k) :
    affineCoefficientMap n k 0 (1 : Matrix (Fin n) (Fin n) ℝ) F = F := by
  apply coefficient_ext
  intro x
  rw [phase_affineCoefficientMap, phase_zero, sub_zero]
  have hx : affinePoint 0 (1 : Matrix (Fin n) (Fin n) ℝ) x = x := by
    change 0 + (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x = x
    simp
  rw [hx]

theorem affineCoefficientMap_inverse_left (n k : ℕ) (c : (PhysicalSpace n))
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (F : CoefficientSpace n k) :
    affineCoefficientMap n k (-(B⁻¹ *ᵥ c)) B⁻¹ (affineCoefficientMap n k c B F) = F := by
  rw [affineCoefficientMap_comp, B.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hB)]
  have hc : c + B *ᵥ (-(B⁻¹ *ᵥ c)) = 0 := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      B.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec]
    exact add_neg_cancel c
  rw [hc, affineCoefficientMap_identity]

theorem affineCoefficientMap_inverse_right (n k : ℕ) (c : (PhysicalSpace n))
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (F : CoefficientSpace n k) :
    affineCoefficientMap n k c B (affineCoefficientMap n k (-(B⁻¹ *ᵥ c)) B⁻¹ F) = F := by
  rw [affineCoefficientMap_comp, B.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hB)]
  rw [neg_add_cancel, affineCoefficientMap_identity]

def affineCoefficientEquiv (n k : ℕ) (c : (PhysicalSpace n))
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) :
    CoefficientSpace n k ≃ₗ[ℝ] CoefficientSpace n k :=
  { affineCoefficientMap n k c B with
    invFun := affineCoefficientMap n k (-(B⁻¹ *ᵥ c)) B⁻¹
    left_inv := affineCoefficientMap_inverse_left n k c B hB
    right_inv := affineCoefficientMap_inverse_right n k c B hB }

end PaperI.AllDim
