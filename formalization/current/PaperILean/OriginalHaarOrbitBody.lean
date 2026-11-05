import PaperILean.OriginalHaarOrbitPolynomial
import PaperILean.NecessitySeedJacobianDifferential
import PaperILean.OriginalUpperBodyFlow
import PaperILean.AugmentedPhysicalAffine
import PaperILean.AffineVectorFieldCoefficient
import Mathlib.Tactic

/-! Actual coefficient-orbit differentiation along the original body velocity.
This identifies the derivative with `[XJ]` before any singular-value bound. -/

noncomputable section
namespace PaperI.OriginalHaarOrbitBody

open scoped BigOperators
open Matrix
open OriginalHaarOrbitPolynomial

abbrev Upper := Fin 6 → ℝ

theorem contDiff_orbit {k : ℕ} (F : CoefficientSpace k) :
    ContDiff ℝ ⊤ (originalUpperCoefficientPullback F) := by
  have hc : ContDiff ℝ ⊤ (fun g : Upper => (![g 2,g 4,g 5] : PhysicalSpace)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hB : ContDiff ℝ ⊤
      (fun g : Upper => fun i j : Fin 3 => originalUpperLinearMatrix g i j) := by
    rw [contDiff_pi]
    intro i
    rw [contDiff_pi]
    intro j
    fin_cases i <;> fin_cases j <;> simp [originalUpperLinearMatrix] <;> fun_prop
  simpa only [originalUpperCoefficientPullback] using
    NecessitySeedJacobian.contDiff_affineCoefficientMap_joint
      (fun g : Upper => (![g 2,g 4,g 5] : PhysicalSpace))
      (fun g : Upper => fun i j : Fin 3 => originalUpperLinearMatrix g i j)
      (fun _ : Upper => F) hc hB contDiff_const

def phaseEvaluation (k : ℕ) (x : PhysicalSpace) : CoefficientSpace k →L[ℝ] ℝ :=
  ∑ α : MonomialIndex k, (∏ i : Fin 3, x i ^ (α.val i).val) • ContinuousLinearMap.proj α

theorem phaseEvaluation_apply {k : ℕ} (x : PhysicalSpace) (F : CoefficientSpace k) :
    phaseEvaluation k x F = phase F x := by
  classical
  simp [phaseEvaluation, phase, mul_comm]

/-- The derivative of evaluation at a fixed physical point with respect to the six group coordinates. -/
def evaluationDifferential (x : PhysicalSpace) : Upper →L[ℝ] PhysicalSpace :=
  ContinuousLinearMap.pi
    ![x 1 • ContinuousLinearMap.proj 0 + x 2 • ContinuousLinearMap.proj 1 +
        ContinuousLinearMap.proj 2,
      x 2 • ContinuousLinearMap.proj 3 + ContinuousLinearMap.proj 4,
      ContinuousLinearMap.proj 5]

theorem evaluationDifferential_apply (x : PhysicalSpace) (v : Upper) :
    evaluationDifferential x v =
      ![v 0 * x 1 + v 1 * x 2 + v 2, v 3 * x 2 + v 4, v 5] := by
  ext i
  fin_cases i <;> simp [evaluationDifferential] <;> ring

theorem evaluation_eq (g : Upper) (x : PhysicalSpace) :
    originalUpperAffineEval g x = x + evaluationDifferential x g := by
  ext i
  fin_cases i <;> simp [originalUpperAffineEval, evaluationDifferential_apply] <;> ring

theorem hasFDerivAt_evaluation (g : Upper) (x : PhysicalSpace) :
    HasFDerivAt (fun u : Upper => originalUpperAffineEval u x)
      (evaluationDifferential x) g := by
  simp_rw [evaluation_eq]
  simpa only [zero_add] using
    (hasFDerivAt_const x g).add (evaluationDifferential x).hasFDerivAt

theorem evaluation_zero (g : Upper) :
    originalUpperAffineEval g 0 = ![g 2,g 4,g 5] := by
  ext i
  fin_cases i <;> simp [originalUpperAffineEval]

theorem evaluationDifferential_body (g b : Upper) (x : PhysicalSpace) :
    evaluationDifferential x (originalUpperBodyVelocity g b) =
      originalUpperLinearMatrix g *ᵥ
        (upperAffineFieldTranslation b + upperAffineFieldLinear b *ᵥ x) := by
  ext i
  fin_cases i <;>
    simp [evaluationDifferential_apply, originalUpperBodyVelocity,
      upperAffineFieldTranslation, upperAffineFieldLinear, originalUpperLinearMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem fderiv_orbit_phase {k : ℕ} (F : CoefficientSpace k)
    (g v : Upper) (x : PhysicalSpace) :
    phase (fderiv ℝ (originalUpperCoefficientPullback F) g v) x =
      polynomialDifferential (coefficientPolynomial F) (originalUpperAffineEval g x)
        (evaluationDifferential x v) -
      polynomialDifferential (coefficientPolynomial F) (originalUpperAffineEval g 0)
        (evaluationDifferential 0 v) := by
  have ho := (((contDiff_orbit F).differentiable (by simp)) g).hasFDerivAt
  have hq : HasFDerivAt
      (fun u : Upper => phase (originalUpperCoefficientPullback F u) x)
      ((phaseEvaluation k x).comp (fderiv ℝ (originalUpperCoefficientPullback F) g)) g := by
    simpa only [Function.comp_def, phaseEvaluation_apply] using
      (phaseEvaluation k x).hasFDerivAt.comp g ho
  have hp := ((hasFDerivAt_phase F (originalUpperAffineEval g x)).comp g
      (hasFDerivAt_evaluation g x)).sub
    ((hasFDerivAt_phase F (originalUpperAffineEval g 0)).comp g
      (hasFDerivAt_evaluation g 0))
  have hfun : (fun u : Upper => phase (originalUpperCoefficientPullback F u) x) =
      fun u => phase F (originalUpperAffineEval u x) - phase F (originalUpperAffineEval u 0) := by
    funext u
    rw [originalUpperCoefficientPullback_phase, evaluation_zero]
  rw [hfun] at hq
  have he := congrArg (fun L : Upper →L[ℝ] ℝ => L v) (hq.unique hp)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    phaseEvaluation_apply] using he

/-- The body's infinitesimal quotient action is the actual affine vector-field action. -/
theorem fderiv_orbit_body {k : ℕ} (F : CoefficientSpace k) (g b : Upper) :
    fderiv ℝ (originalUpperCoefficientPullback F) g (originalUpperBodyVelocity g b) =
      affineFieldCoefficientMap k (upperAffineFieldTranslation b) (upperAffineFieldLinear b)
        (originalUpperCoefficientPullback F g) := by
  apply coefficient_ext
  intro x
  rw [fderiv_orbit_phase, phase_affineFieldCoefficientMap]
  simp only [originalUpperCoefficientPullback,
    (hasFDerivAt_phase_affine k ![g 2,g 4,g 5] (originalUpperLinearMatrix g) F x).fderiv,
    (hasFDerivAt_phase_affine k ![g 2,g 4,g 5] (originalUpperLinearMatrix g) F 0).fderiv,
    ContinuousLinearMap.comp_apply, frameLinearMap_apply]
  rw [evaluationDifferential_body, evaluationDifferential_body]
  simp only [Matrix.mulVec_zero, add_zero]
  rw [← originalUpperAffineEval_eq_affinePoint, ← originalUpperAffineEval_eq_affinePoint]

/-- The complete body chain rule along an actual differentiable group path. -/
theorem orbit_hasDerivAt_body {k : ℕ} (F : CoefficientSpace k)
    (g : ℝ → Upper) (v : Upper) (t : ℝ) (hg : HasDerivAt g v t) :
    HasDerivAt (fun s => originalUpperCoefficientPullback F (g s))
      (affineFieldCoefficientMap k
        (upperAffineFieldTranslation (originalAffineBodyCoordinates (g t) v))
        (upperAffineFieldLinear (originalAffineBodyCoordinates (g t) v))
        (originalUpperCoefficientPullback F (g t))) t := by
  have ho := ((((contDiff_orbit F).differentiable (by simp)) (g t)).hasFDerivAt).comp_hasDerivAt t hg
  have hb := fderiv_orbit_body F (g t) (originalAffineBodyCoordinates (g t) v)
  rw [originalUpperBodyVelocity_body] at hb
  rw [hb] at ho
  exact ho

theorem orbit_coordinate_hasDerivAt_body {k : ℕ} (F : CoefficientSpace k)
    (g : ℝ → Upper) (v : Upper) (t : ℝ) (hg : HasDerivAt g v t)
    (α : MonomialIndex k) :
    HasDerivAt (fun s => originalUpperCoefficientPullback F (g s) α)
      (affineFieldCoefficientMap k
        (upperAffineFieldTranslation (originalAffineBodyCoordinates (g t) v))
        (upperAffineFieldLinear (originalAffineBodyCoordinates (g t) v))
        (originalUpperCoefficientPullback F (g t)) α) t := by
  exact (ContinuousLinearMap.proj α).hasFDerivAt.comp_hasDerivAt t
    (orbit_hasDerivAt_body F g v t hg)

end PaperI.OriginalHaarOrbitBody
