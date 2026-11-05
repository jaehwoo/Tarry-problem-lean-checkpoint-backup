import PaperILean.SingularValueEuclideanBounds
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-! The literal left pseudoinverse from I1341, used in the regular d-section
rates at I3239--I3242.  The inverse identity is proved from injectivity of the
actual rectangular matrix; the quantitative wrapper keeps its positive
least-singular-value lower bound. -/

noncomputable section
namespace PaperI.RegularSectionPseudoinverse

open scoped Matrix

/-- The manuscript's explicit formula, with the column coordinates unchanged. -/
noncomputable def leftPseudoinverse {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (L : Matrix m n ℝ) : Matrix n m ℝ :=
  (L.transpose * L)⁻¹ * L.transpose

/-- Full column rank makes the literal Gram inverse a left inverse. -/
theorem leftPseudoinverse_mul_of_injective {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (L : Matrix m n ℝ) (hL : Function.Injective L.mulVec) :
    leftPseudoinverse L * L = 1 := by
  classical
  have hI : (1 : Matrix m m ℝ).PosDef := Matrix.PosDef.one
  have hgram : (L.transpose * L).PosDef := by
    simpa only [Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hI.conjTranspose_mul_mul_same (B := L) hL
  rw [leftPseudoinverse, Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ hgram.det_pos.ne'.isUnit

/-- A positive quantitative singular-value bound proves actual column
injectivity, using the saved Euclidean lower norm inequality. -/
theorem mulVec_injective_of_singular_lower {m : Type*} [Fintype m] {n : ℕ}
    (L : Matrix m (Fin (n + 1)) ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hL : σ ≤ descendingSingularValues L (Fin.last n)) :
    Function.Injective L.mulVec := by
  have hinj : Function.Injective (Matrix.toEuclideanLin L) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hbound := (le_least_descendingSingularValue_iff L σ).mp hL x
    rw [hx, norm_zero] at hbound
    have hnorm : ‖x‖ = 0 := by
      nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hnorm
  intro x y hxy
  apply (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm.injective
  apply hinj
  simp only [Matrix.toEuclideanLin_apply_piLp_equiv_symm, hxy]

/-- The actual matrix inverse identity with the source's positive quantitative
least-singular-value hypothesis retained explicitly. -/
theorem leftPseudoinverse_mul_of_singular_lower {m : Type*} [Fintype m] {n : ℕ}
    (L : Matrix m (Fin (n + 1)) ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hL : σ ≤ descendingSingularValues L (Fin.last n)) :
    leftPseudoinverse L * L = 1 :=
  leftPseudoinverse_mul_of_injective L
    (mulVec_injective_of_singular_lower L σ hσ hL)

end PaperI.RegularSectionPseudoinverse
