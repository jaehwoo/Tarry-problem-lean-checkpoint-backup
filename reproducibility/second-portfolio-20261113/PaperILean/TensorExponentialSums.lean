import PaperILean.FrameExponentialSpectral
import PaperILean.ExponentialSumCalculus

/-! The actual raw affine tensors along B exp(t H), Paper I248. Each ordered
word is retained. The identities hold for every order, including order zero,
and do not require a nonzero tensor, distinct eigenvalues, or an invertible B. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem jetTensorHSNorm_sq {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) :
    (jetTensorHSNorm F c B r) ^ 2 = ∑ a : Fin r → Fin 3, (jetTensorComponent F c B r a) ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg _))

theorem jetTensorComponent_mul_diagonal {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ) (r : ℕ) (a : Fin r → Fin 3) :
    jetTensorComponent F c (B * Matrix.diagonal d) r a =
      jetTensorComponent F c B r a * ∏ j, d (a j) := by
  unfold jetTensorComponent
  have hv : (fun j : Fin r => (B * Matrix.diagonal d) *ᵥ Pi.single (a j) (1 : ℝ)) =
      (fun j : Fin r => d (a j) • (B *ᵥ Pi.single (a j) (1 : ℝ))) := by
    funext j i
    simp only [Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.mul_diagonal,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [hv, ContinuousMultilinearMap.map_smul_univ]
  simp only [smul_eq_mul, mul_comm]

theorem jetTensorComponent_mul_exp_diagonal {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ)
    (r : ℕ) (a : Fin r → Fin 3) (t : ℝ) :
    jetTensorComponent F c (B * Matrix.diagonal (fun i => Real.exp (t * d i))) r a =
      jetTensorComponent F c B r a * Real.exp (t * ∑ j, d (a j)) := by
  rw [jetTensorComponent_mul_diagonal, Finset.mul_sum, Real.exp_sum]

theorem jetTensorHSNorm_exp_eq_sum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm)
    (r : ℕ) (t : ℝ) :
    (jetTensorHSNorm F c (B * NormedSpace.exp ℝ (t • H)) r) ^ 2 =
      ∑ a : Fin r → Fin 3,
        (jetTensorComponent F c (B * (symmetricFrameEigenbasis H hH : Matrix (Fin 3) (Fin 3) ℝ)) r a) ^ 2 *
          Real.exp (t * (2 * ∑ j, symmetricFrameEigenvalues H hH (a j))) := by
  rw [matrix_exp_symmetricFrame_spectral H hH t]
  unfold orthogonalConjugate
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, jetTensorHSNorm_right_orthogonal F c _ _
    (by simpa only [Matrix.transpose_transpose] using
      real_unitary_transpose_mul (symmetricFrameEigenbasis H hH)), jetTensorHSNorm_sq]
  apply Finset.sum_congr rfl
  intro a _
  rw [jetTensorComponent_mul_exp_diagonal, mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

theorem jetTensorHSNorm_exp_convex {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (r : ℕ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => (jetTensorHSNorm F c (B * NormedSpace.exp ℝ (t • H)) r) ^ 2) := by
  have heq : (fun t : ℝ => (jetTensorHSNorm F c (B * NormedSpace.exp ℝ (t • H)) r) ^ 2) =
      weightedExponentialSum Finset.univ
        (fun a : Fin r → Fin 3 =>
          (jetTensorComponent F c (B * (symmetricFrameEigenbasis H hH : Matrix (Fin 3) (Fin 3) ℝ)) r a) ^ 2)
        (fun a => 2 * ∑ j, symmetricFrameEigenvalues H hH (a j)) := by
    funext t
    exact jetTensorHSNorm_exp_eq_sum F c B H hH r t
  rw [heq]
  exact weightedExponentialSum_convex _ _ _ (fun a _ => sq_nonneg _)

end PaperI
