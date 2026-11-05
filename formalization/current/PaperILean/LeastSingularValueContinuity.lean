import PaperILean.SingularValueEuclideanBounds
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! I600 and I683: operator-norm perturbation and continuity of the actual
least ordered Euclidean singular value, including repeated values and kernels.
This does not assert continuity of the fourth value of the six-column map. -/

noncomputable section
namespace PaperI

variable {m : Type*} [Fintype m] {n : ℕ}

/-- Exact Euclidean realization with the continuous-linear operator norm. -/
def rectangularEuclideanCLM :
    Matrix m (Fin n) ℝ ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ m) :=
  Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap

theorem rectangularEuclideanCLM_apply (A : Matrix m (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    rectangularEuclideanCLM A x = Matrix.toEuclideanLin A x := rfl

theorem continuous_rectangularEuclideanCLM :
    Continuous (rectangularEuclideanCLM : Matrix m (Fin n) ℝ →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ m)) :=
  (rectangularEuclideanCLM (m := m) (n := n)).toLinearMap.continuous_of_finiteDimensional

theorem least_descendingSingularValue_le_add_opNorm
    (A B : Matrix m (Fin (n + 1)) ℝ) :
    descendingSingularValues A (Fin.last n) ≤
      descendingSingularValues B (Fin.last n) +
        ‖rectangularEuclideanCLM A - rectangularEuclideanCLM B‖ := by
  obtain ⟨x, hx, hBx⟩ := descendingSingularValue_exists_unit_vector B (Fin.last n)
  have ha := least_descendingSingularValue_mul_norm_le A x
  rw [hx, mul_one] at ha
  have hop := (rectangularEuclideanCLM A - rectangularEuclideanCLM B).le_opNorm x
  rw [hx, mul_one] at hop
  have ht := norm_add_le
    ((rectangularEuclideanCLM A - rectangularEuclideanCLM B) x)
    (rectangularEuclideanCLM B x)
  simp only [ContinuousLinearMap.sub_apply, sub_add_cancel,
    rectangularEuclideanCLM_apply, hBx] at ht
  simp only [ContinuousLinearMap.sub_apply, rectangularEuclideanCLM_apply] at hop
  exact ha.trans (ht.trans (by linarith))

theorem abs_least_descendingSingularValue_sub_le
    (A B : Matrix m (Fin (n + 1)) ℝ) :
    |descendingSingularValues A (Fin.last n) -
        descendingSingularValues B (Fin.last n)| ≤
      ‖rectangularEuclideanCLM A - rectangularEuclideanCLM B‖ := by
  have hab := least_descendingSingularValue_le_add_opNorm A B
  have hba := least_descendingSingularValue_le_add_opNorm B A
  rw [norm_sub_rev] at hba
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem continuous_least_descendingSingularValue :
    Continuous (fun A : Matrix m (Fin (n + 1)) ℝ =>
      descendingSingularValues A (Fin.last n)) := by
  let e : Matrix m (Fin (n + 1)) ℝ ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ m) :=
    rectangularEuclideanCLM
  have hlip : LipschitzWith 1 (fun T : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ m => descendingSingularValues (e.symm T) (Fin.last n)) := by
    apply LipschitzWith.of_dist_le_mul
    intro T U
    have h := abs_least_descendingSingularValue_sub_le (e.symm T) (e.symm U)
    change |descendingSingularValues (e.symm T) (Fin.last n) -
      descendingSingularValues (e.symm U) (Fin.last n)| ≤ ‖e (e.symm T) - e (e.symm U)‖ at h
    simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul,
      LinearEquiv.apply_symm_apply] using h
  have hcomp := hlip.continuous.comp e.toLinearMap.continuous_of_finiteDimensional
  change Continuous (fun A => descendingSingularValues (e.symm (e A)) (Fin.last n)) at hcomp
  simpa only [LinearEquiv.symm_apply_apply] using hcomp


end PaperI
