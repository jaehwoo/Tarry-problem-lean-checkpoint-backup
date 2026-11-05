import PaperILean.NormalFibersStage
import PaperILean.NormalJacobianDifferential
import PaperILean.NormalJacobianDeterminant

/-! Completion of the entire source lemma I3258--I3277.  The saved count is
reused; the new work is the actual transverse Jacobian in I3263--I3265/I3276.
Every public manuscript statement retains the full normalized-frame predicate.
-/

noncomputable section
namespace PaperI.NormalFibers

/-- Signed chart-I determinant of the actual four defining equations. -/
theorem signed_jacobian_chartI (G : Poly) (e f : ℝ) (w : FrameSpace)
    (hw : w ∈ normalizedFrames G e f) :
    (ordinaryJacobian (normalizationEquationsI G e f) w).det =
      (MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (pullback w e f G))) ^ 3 *
        MvPolynomial.eval 0
          (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (pullback w e f G))) := by
  have hn : w 1 * firstAt G e f 0 (w 0) + firstAt G e f 1 (w 0) = 0 := by
    simpa only [first_y] using hw.2.2.1
  rw [ordinaryJacobian_normalizationEquationsI, first_x, second_yy]
  exact det_normalizationMatrix_chartI _ _ _ _ _ _ _ _ _ _ hn

/-- Signed chart-II determinant, including the derivative's factor two. -/
theorem signed_jacobian_chartII (G : Poly) (e f : ℝ) (w : FrameSpace)
    (hw : w ∈ normalizedFrames G e f) :
    (ordinaryJacobian (normalizationEquationsII G e f) w).det =
      2 * (MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (pullback w e f G))) ^ 3 *
        MvPolynomial.eval 0
          (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (pullback w e f G))) := by
  have hn : w 1 * firstAt G e f 0 (w 0) + firstAt G e f 1 (w 0) = 0 := by
    simpa only [first_y] using hw.2.2.1
  rw [ordinaryJacobian_normalizationEquationsII, first_x, second_yz]
  exact det_normalizationMatrix_chartII _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn

/-- Entire part(ii): actual differentiability and both ordinary absolute
Jacobian formulas.  The full source hypotheses remain in `hw`; in particular
the constants, fixed center, regularity and alternative chart pivots remain.
Both identities hold at either source-normalized frame. -/
theorem normal_transverse_jacobians (G : Poly) (e f : ℝ) (w : FrameSpace)
    (hw : w ∈ normalizedFrames G e f) :
    DifferentiableAt ℝ (normalizationEquationsI G e f) w ∧
    DifferentiableAt ℝ (normalizationEquationsII G e f) w ∧
    |(ordinaryJacobian (normalizationEquationsI G e f) w).det| =
      |MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (pullback w e f G))| ^ 3 *
        |MvPolynomial.eval 0
          (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (pullback w e f G)))| ∧
    |(ordinaryJacobian (normalizationEquationsII G e f) w).det| =
      2 * |MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (pullback w e f G))| ^ 3 *
        |MvPolynomial.eval 0
          (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (pullback w e f G)))| := by
  refine ⟨(hasFDerivAt_normalizationEquationsI G e f w).differentiableAt,
    (hasFDerivAt_normalizationEquationsII G e f w).differentiableAt, ?_, ?_⟩
  · rw [signed_jacobian_chartI G e f w hw, abs_mul, abs_pow]
  · rw [signed_jacobian_chartII G e f w hw, abs_mul, abs_mul, abs_pow]
    norm_num

end PaperI.NormalFibers

namespace PaperI
open NormalFibers

/-- The whole finite-normal-fibers and transverse-Jacobians lemma,
I3258--I3277, with no external or unresolved project premise. -/
theorem finite_normal_fibers_and_transverse_jacobians
    (G : MvPolynomial (Fin 3) ℝ) (D : ℕ) (hdegree : G.totalDegree ≤ D) (e f : ℝ) :
    ((normalizedFrames G e f).Finite ∧ (normalizedFrames G e f).ncard ≤ 3 * D) ∧
    ∀ w ∈ normalizedFrames G e f,
      DifferentiableAt ℝ (normalizationEquationsI G e f) w ∧
      DifferentiableAt ℝ (normalizationEquationsII G e f) w ∧
      |(ordinaryJacobian (normalizationEquationsI G e f) w).det| =
        |MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (pullback w e f G))| ^ 3 *
          |MvPolynomial.eval 0
            (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (pullback w e f G)))| ∧
      |(ordinaryJacobian (normalizationEquationsII G e f) w).det| =
        2 * |MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (pullback w e f G))| ^ 3 *
          |MvPolynomial.eval 0
            (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (pullback w e f G)))| := by
  exact ⟨finite_normal_fibers_stage G D hdegree e f,
    fun w hw => normal_transverse_jacobians G e f w hw⟩

end PaperI
