import PaperILean.AllDimAffinePullback
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection

/-! Orthogonal intermediate in the manuscript's SVD proof. The omitted
orthogonal detail is supplied by Cartan--Dieudonne, using involutivity of
reflections. No general coefficient determinant character is used.

Boundary checks before this strategy: empty dimension and degree zero give an
empty coefficient basis; signed determinant one is false for reflections, so
the result is stated with absolute value; no distinct-eigenvalue condition is
needed; the unweighted monomial coefficient norm is not asserted invariant. -/

noncomputable section
namespace PaperI.AllDim.Original
open Matrix

theorem coefficient_det_dim_zero (k : ℕ) (c : PhysicalSpace 0)
    (A : Matrix (Fin 0) (Fin 0) ℝ) :
    LinearMap.det (affineCoefficientMap 0 k c A) = 1 :=
  LinearMap.det_eq_one_of_subsingleton _

theorem coefficient_det_degree_zero (n : ℕ) (c : PhysicalSpace n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (affineCoefficientMap n 0 c A) = 1 :=
  LinearMap.det_eq_one_of_subsingleton _

theorem centeredCoefficientMap_det_mul_original (n k : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (affineCoefficientMap n k 0 (A * B)) =
      LinearMap.det (affineCoefficientMap n k 0 A) *
      LinearMap.det (affineCoefficientMap n k 0 B) := by
  have h : affineCoefficientMap n k 0 (A * B) =
      (affineCoefficientMap n k 0 B).comp (affineCoefficientMap n k 0 A) := by
    apply LinearMap.ext
    intro F
    simpa using (affineCoefficientMap_comp n k 0 0 A B F).symm
  rw [h, LinearMap.det_comp, mul_comm]

theorem centeredCoefficientMap_det_one_original (n k : ℕ) :
    LinearMap.det (affineCoefficientMap n k 0 (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
  have h : affineCoefficientMap n k 0 (1 : Matrix (Fin n) (Fin n) ℝ) = LinearMap.id := by
    apply LinearMap.ext
    intro F
    exact affineCoefficientMap_identity n k F
  rw [h, LinearMap.det_id]

theorem centeredCoefficientMap_involution_abs_det (n k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A * A = 1) :
    |LinearMap.det (affineCoefficientMap n k 0 A)| = 1 := by
  have h := centeredCoefficientMap_det_mul_original n k A A
  rw [hA, centeredCoefficientMap_det_one_original] at h
  have hs : |LinearMap.det (affineCoefficientMap n k 0 A)| ^ 2 = 1 := by
    rw [sq_abs, pow_two, ← h]
  nlinarith [abs_nonneg (LinearMap.det (affineCoefficientMap n k 0 A))]

abbrev OriginalEuclideanSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

def isometryMatrix {n : ℕ}
    (e : OriginalEuclideanSpace n ≃ₗᵢ[ℝ] OriginalEuclideanSpace n) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin n)) (PiLp.basisFun 2 ℝ (Fin n)) e.toLinearMap

theorem isometryMatrix_mul {n : ℕ}
    (e f : OriginalEuclideanSpace n ≃ₗᵢ[ℝ] OriginalEuclideanSpace n) :
    isometryMatrix (e * f) = isometryMatrix e * isometryMatrix f := by
  exact LinearMap.toMatrix_mul (PiLp.basisFun 2 ℝ (Fin n)) e.toLinearMap f.toLinearMap

theorem isometryMatrix_one (n : ℕ) :
    isometryMatrix (1 : OriginalEuclideanSpace n ≃ₗᵢ[ℝ] OriginalEuclideanSpace n) = 1 := by
  exact LinearMap.toMatrix_one (PiLp.basisFun 2 ℝ (Fin n))

theorem isometryMatrix_orthogonal {n : ℕ}
    (e : OriginalEuclideanSpace n ≃ₗᵢ[ℝ] OriginalEuclideanSpace n) :
    (isometryMatrix e).transpose * isometryMatrix e = 1 := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hm : isometryMatrix e = b.toBasis.toMatrix (b.map e) := by
    ext i j
    simp only [isometryMatrix, LinearMap.toMatrix_apply, Basis.toMatrix_apply,
      OrthonormalBasis.map_apply]
    rfl
  rw [hm]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    b.toMatrix_orthonormalBasis_conjTranspose_mul_self (b.map e)

theorem toEuclideanLin_isometryMatrix {n : ℕ}
    (e : OriginalEuclideanSpace n ≃ₗᵢ[ℝ] OriginalEuclideanSpace n) :
    Matrix.toEuclideanLin (isometryMatrix e) = e.toLinearMap := by
  rw [Matrix.toEuclideanLin_eq_toLin, isometryMatrix, Matrix.toLin_toMatrix]

theorem isometryMatrix_abs_det_coefficient (n k : ℕ)
    (e : OriginalEuclideanSpace n ≃ₗᵢ[ℝ] OriginalEuclideanSpace n) :
    |LinearMap.det (affineCoefficientMap n k 0 (isometryMatrix e))| = 1 := by
  obtain ⟨l, hlen, hl⟩ := e.reflections_generate_dim
  rw [hl]
  clear hlen hl e
  induction l with
  | nil => simp [isometryMatrix_one, centeredCoefficientMap_det_one_original]
  | cons v l ih =>
    simp only [List.map_cons, List.prod_cons, isometryMatrix_mul,
      centeredCoefficientMap_det_mul_original, abs_mul, ih, mul_one]
    apply centeredCoefficientMap_involution_abs_det
    rw [← isometryMatrix_mul, Submodule.reflection_mul_reflection, isometryMatrix_one]

def matrixOrthogonalIsometry (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose * A = 1) : OriginalEuclideanSpace n ≃ₗᵢ[ℝ] OriginalEuclideanSpace n := by
  let f := Matrix.toEuclideanLin A
  let g := Matrix.toEuclideanLin A.transpose
  have hAf : A * A.transpose = 1 := mul_eq_one_comm.mp hA
  let e : OriginalEuclideanSpace n ≃ₗ[ℝ] OriginalEuclideanSpace n :=
    { f with
      invFun := g
      left_inv := by
        intro x
        apply (WithLp.equiv 2 (Fin n → ℝ)).injective
        change A.transpose *ᵥ (A *ᵥ _) = _
        rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
        rfl
      right_inv := by
        intro x
        apply (WithLp.equiv 2 (Fin n → ℝ)).injective
        change A *ᵥ (A.transpose *ᵥ _) = _
        rw [Matrix.mulVec_mulVec, hAf, Matrix.one_mulVec]
        rfl }
  apply e.isometryOfInner
  intro x y
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change (A *ᵥ _) ⬝ᵥ (A *ᵥ _) = _
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hA, Matrix.vecMul_one]
  rfl

theorem isometryMatrix_matrixOrthogonalIsometry (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.transpose * A = 1) :
    isometryMatrix (matrixOrthogonalIsometry n A hA) = A := by
  change LinearMap.toMatrix _ _ (Matrix.toEuclideanLin A) = A
  rw [Matrix.toEuclideanLin_eq_toLin, LinearMap.toMatrix_toLin]

theorem affineCoefficientMap_orthogonal_abs_det_original (n k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.transpose * A = 1) :
    |LinearMap.det (affineCoefficientMap n k 0 A)| = 1 := by
  have h := isometryMatrix_abs_det_coefficient n k (matrixOrthogonalIsometry n A hA)
  rwa [isometryMatrix_matrixOrthogonalIsometry] at h

#print axioms coefficient_det_dim_zero
#print axioms coefficient_det_degree_zero
#print axioms centeredCoefficientMap_det_mul_original
#print axioms centeredCoefficientMap_det_one_original
#print axioms centeredCoefficientMap_involution_abs_det
#print axioms isometryMatrix
#print axioms isometryMatrix_mul
#print axioms isometryMatrix_one
#print axioms isometryMatrix_orthogonal
#print axioms toEuclideanLin_isometryMatrix
#print axioms isometryMatrix_abs_det_coefficient
#print axioms matrixOrthogonalIsometry
#print axioms isometryMatrix_matrixOrthogonalIsometry
#print axioms affineCoefficientMap_orthogonal_abs_det_original
end PaperI.AllDim.Original
