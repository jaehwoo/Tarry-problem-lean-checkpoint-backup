import PaperILean.AffinePullback
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

open MvPolynomial Matrix

namespace PaperI.AffineDefiningPolynomial

/-- The raw defining equation in physical coordinates. Its constant coefficient is retained. -/
noncomputable def transformedEquation (b : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (G : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  affinePolynomialMap (-B⁻¹.mulVec b) B⁻¹ G

def zeroSet (G : MvPolynomial (Fin 3) ℝ) : Set PhysicalSpace :=
  {x | MvPolynomial.eval x G = 0}

theorem affinePoint_eq (b : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (x : PhysicalSpace) : affinePoint b B x = b + B.mulVec x := rfl

theorem affinePoint_identity (x : PhysicalSpace) : affinePoint 0 1 x = x := by
  rw [affinePoint_eq, Matrix.one_mulVec, zero_add]

theorem inverse_point_left (b : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.det ≠ 0) (x : PhysicalSpace) :
    affinePoint (-B⁻¹.mulVec b) B⁻¹ (affinePoint b B x) = x := by
  rw [affinePoint_comp, Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB)]
  simpa only [neg_add_cancel] using affinePoint_identity x

theorem inverse_point_right (b : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.det ≠ 0) (x : PhysicalSpace) :
    affinePoint b B (affinePoint (-B⁻¹.mulVec b) B⁻¹ x) = x := by
  rw [affinePoint_comp, Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB),
    Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec, add_neg_cancel]
  exact affinePoint_identity x

theorem transformed_equation_eval (b : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (G : MvPolynomial (Fin 3) ℝ) (x : PhysicalSpace) :
    MvPolynomial.eval x (transformedEquation b B G) =
      MvPolynomial.eval (affinePoint (-B⁻¹.mulVec b) B⁻¹ x) G :=
  eval_affinePolynomialMap _ _ _ _

theorem transformed_equation_eval_image (b : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.det ≠ 0) (G : MvPolynomial (Fin 3) ℝ) (x : PhysicalSpace) :
    MvPolynomial.eval (affinePoint b B x) (transformedEquation b B G) =
      MvPolynomial.eval x G := by
  rw [transformed_equation_eval, inverse_point_left b B hB]

theorem raw_forward_inverse (b : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.det ≠ 0) (G : MvPolynomial (Fin 3) ℝ) :
    affinePolynomialMap b B (transformedEquation b B G) = G := by
  apply MvPolynomial.funext
  intro x
  rw [eval_affinePolynomialMap, transformed_equation_eval_image b B hB]

theorem raw_inverse_forward (b : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.det ≠ 0) (G : MvPolynomial (Fin 3) ℝ) :
    transformedEquation b B (affinePolynomialMap b B G) = G := by
  apply MvPolynomial.funext
  intro x
  rw [transformed_equation_eval, eval_affinePolynomialMap, inverse_point_right b B hB]

/-- Both inequalities are instances of the previously accepted raw affine degree bound. -/
theorem transformed_equation_degree (b : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.det ≠ 0) (G : MvPolynomial (Fin 3) ℝ) :
    (transformedEquation b B G).totalDegree = G.totalDegree := by
  apply le_antisymm (affinePolynomialMap_degree _ _ _)
  have h := affinePolynomialMap_degree b B (transformedEquation b B G)
  rw [raw_forward_inverse b B hB G] at h
  exact h

theorem transformed_equation_ne_zero_iff (b : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.det ≠ 0) (G : MvPolynomial (Fin 3) ℝ) :
    transformedEquation b B G ≠ 0 ↔ G ≠ 0 := by
  constructor
  · intro h hz
    subst G
    exact h (map_zero _)
  · intro h hz
    have hr := raw_forward_inverse b B hB G
    rw [hz, map_zero] at hr
    exact h hr.symm

theorem transformed_equation_zeroSet (b : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.det ≠ 0) (G : MvPolynomial (Fin 3) ℝ) :
    zeroSet (transformedEquation b B G) = affinePoint b B '' zeroSet G := by
  ext y
  constructor
  · intro hy
    refine ⟨affinePoint (-B⁻¹.mulVec b) B⁻¹ y, ?_, inverse_point_right b B hB y⟩
    change MvPolynomial.eval y (transformedEquation b B G) = 0 at hy
    change MvPolynomial.eval (affinePoint (-B⁻¹.mulVec b) B⁻¹ y) G = 0
    rwa [transformed_equation_eval] at hy
  · rintro ⟨x, hx, rfl⟩
    change MvPolynomial.eval (affinePoint b B x) (transformedEquation b B G) = 0
    rw [transformed_equation_eval_image b B hB]
    exact hx

/-- I3339[44,101): the physical defining polynomial is nonzero, has exactly the
original degree, and defines the affine image of the original real zero set. -/
theorem affine_defining_polynomial_stage (b : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.det ≠ 0) (G : MvPolynomial (Fin 3) ℝ) (hG : G ≠ 0)
    (D : ℕ) (hD : G.totalDegree ≤ D) :
    transformedEquation b B G ≠ 0 ∧
    (transformedEquation b B G).totalDegree = G.totalDegree ∧
    (transformedEquation b B G).totalDegree ≤ D ∧
    zeroSet (transformedEquation b B G) = affinePoint b B '' zeroSet G ∧
    (∀ x : PhysicalSpace,
      MvPolynomial.eval (affinePoint b B x) (transformedEquation b B G) =
        MvPolynomial.eval x G) := by
  refine ⟨(transformed_equation_ne_zero_iff b B hB G).2 hG,
    transformed_equation_degree b B hB G, ?_,
    transformed_equation_zeroSet b B hB G, transformed_equation_eval_image b B hB G⟩
  rw [transformed_equation_degree b B hB G]
  exact hD

end PaperI.AffineDefiningPolynomial
