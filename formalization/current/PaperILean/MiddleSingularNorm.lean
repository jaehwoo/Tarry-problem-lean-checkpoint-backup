import PaperILean.OrderedSingularBasis
import PaperILean.RankOneMatrixFactor

/-! The literal rectangular Frobenius norm and full physical-action bridge
used in the two-dimensional contraction stage at I3253. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix
namespace PaperI.MiddleSingularNorm

noncomputable def matrixFrobenius (A : Matrix (Fin 3) (Fin 4) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

theorem matrixFrobenius_nonneg (A : Matrix (Fin 3) (Fin 4) ℝ) :
    0 ≤ matrixFrobenius A := Real.sqrt_nonneg _

theorem matrixFrobenius_sq (A : Matrix (Fin 3) (Fin 4) ℝ) :
    matrixFrobenius A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem euclidean_mul_norm_le_frobenius (A : Matrix (Fin 3) (Fin 4) ℝ)
    (x : EuclideanSpace ℝ (Fin 4)) :
    ‖Matrix.toEuclideanLin A x‖ ≤ matrixFrobenius A * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (matrixFrobenius_nonneg A) (norm_nonneg x))).mp
  simp only [mul_pow, matrixFrobenius_sq, PiLp.norm_sq_eq_of_L2,
    Real.norm_eq_abs, sq_abs, Matrix.piLp_equiv_toEuclideanLin_apply,
    Matrix.mulVec, dotProduct]
  calc
    (∑ i, (∑ j, A i j * x j) ^ 2) ≤
        ∑ i, (∑ j, A i j ^ 2) * (∑ j, x j ^ 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x
    _ = _ := by rw [Finset.sum_mul]

theorem toEuclideanLin_mul_apply (B : Matrix (Fin 3) (Fin 3) ℝ)
    (M : Matrix (Fin 3) (Fin 4) ℝ) (x : EuclideanSpace ℝ (Fin 4)) :
    Matrix.toEuclideanLin (B * M) x =
      Matrix.toEuclideanLin B (Matrix.toEuclideanLin M x) := by
  apply PiLp.ext
  intro i
  change ((B * M) *ᵥ (fun j => x j)) i = (B *ᵥ (M *ᵥ (fun j => x j))) i
  rw [Matrix.mulVec_mulVec]

theorem mul_affineFieldMatrix (B : Matrix (Fin 3) (Fin 3) ℝ)
    (b : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ) :
    B * RankOneAffineMatrix.affineFieldMatrix b N =
      RankOneAffineMatrix.affineFieldMatrix (B *ᵥ b) (B * N) := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [Matrix.mul_apply, RankOneAffineMatrix.affineFieldMatrix_last,
      Matrix.mulVec, dotProduct]
  · simp only [Matrix.mul_apply, RankOneAffineMatrix.affineFieldMatrix_castSucc]

theorem matrixFrobenius_mul_affine (ell : PhysicalAffineData) (b : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixFrobenius (ell.2 * RankOneAffineMatrix.affineFieldMatrix b N) =
      physicalAffineNorm (physicalAffineFieldAction ell b N) := by
  rw [mul_affineFieldMatrix]
  unfold matrixFrobenius physicalAffineNorm physicalAffineFieldAction
  congr 1
  simp only [Fin.sum_univ_castSucc, RankOneAffineMatrix.affineFieldMatrix_castSucc,
    RankOneAffineMatrix.affineFieldMatrix_last, Finset.sum_add_distrib]
  exact add_comm _ _

end PaperI.MiddleSingularNorm
