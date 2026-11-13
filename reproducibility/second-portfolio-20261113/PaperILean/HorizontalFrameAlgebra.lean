import PaperILean.FrameEnergySmoothness
import PaperILean.SymmetricCongruence

/-! I292: exact algebra and differential identities for the horizontal lift.
These statements do not assert existence of a path or global continuation.
All matrix inverses and Gram matrices are the existing matrix operations. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

def horizontalFrameVelocity {n : ℕ} (D B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := (1 / 2 : ℝ) • (D * B⁻¹ᵀ)

def horizontalFrameGenerator {n : ℕ} (D B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := (1 / 2 : ℝ) • (B⁻¹ * D * B⁻¹ᵀ)

theorem horizontalFrameGenerator_isSymm {n : ℕ} (D B : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.IsSymm) : (horizontalFrameGenerator D B).IsSymm := by
  show (horizontalFrameGenerator D B)ᵀ = horizontalFrameGenerator D B
  simp only [horizontalFrameGenerator, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hD.eq, Matrix.mul_assoc]

theorem mul_horizontalFrameGenerator {n : ℕ} (D B : Matrix (Fin n) (Fin n) ℝ)
    (hB : IsUnit B) : B * horizontalFrameGenerator D B = horizontalFrameVelocity D B := by
  have hi := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  simp only [horizontalFrameGenerator, horizontalFrameVelocity, Matrix.mul_smul,
    ← Matrix.mul_assoc, hi, Matrix.one_mul]

theorem horizontalFrameVelocity_gram {n : ℕ} (D B : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.IsSymm) (hB : IsUnit B) :
    horizontalFrameVelocity D B * Bᵀ + B * (horizontalFrameVelocity D B)ᵀ = D := by
  have hi := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have ht : B⁻¹ᵀ * Bᵀ = 1 := by
    rw [← Matrix.transpose_mul, hi, Matrix.transpose_one]
  simp only [horizontalFrameVelocity, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hD.eq,
    Matrix.mul_assoc, ht, Matrix.mul_one]
  rw [← Matrix.mul_assoc, hi, Matrix.one_mul, ← add_smul]
  norm_num

theorem horizontalFrameGenerator_of_gram_velocity {n : ℕ}
    (B S : Matrix (Fin n) (Fin n) ℝ) (hB : IsUnit B) (hS : S.IsSymm) :
    horizontalFrameGenerator (B * S * Bᵀ + B * (B * S)ᵀ) B = S := by
  have hl := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hr : Bᵀ * B⁻¹ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hl, Matrix.transpose_one]
  have he : B * S * Bᵀ + B * (B * S)ᵀ = (2 : ℝ) • (B * S * Bᵀ) := by
    simp only [Matrix.transpose_mul, hS.eq, ← Matrix.mul_assoc, two_smul]
  rw [he, horizontalFrameGenerator]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Matrix.mul_assoc, hl,
    Matrix.one_mul]
  rw [Matrix.mul_assoc, hr, Matrix.mul_one]
  norm_num

theorem hasDerivAt_matrix_transpose {n : ℕ}
    {B : ℝ → Matrix (Fin n) (Fin n) ℝ} {V : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hB : HasDerivAt B V t) : HasDerivAt (fun s => (B s)ᵀ) Vᵀ t :=
  ((Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toContinuousLinearEquiv.hasFDerivAt).comp_hasDerivAt t hB

theorem hasDerivAt_frameGram {n : ℕ}
    {B : ℝ → Matrix (Fin n) (Fin n) ℝ} {V : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hB : HasDerivAt B V t) :
    HasDerivAt (fun s => B s * (B s)ᵀ) (V * (B t)ᵀ + B t * Vᵀ) t :=
  hB.mul (hasDerivAt_matrix_transpose hB)

theorem hasDerivAt_frameGram_horizontal {n : ℕ}
    {B : ℝ → Matrix (Fin n) (Fin n) ℝ} {D : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hB : HasDerivAt B (horizontalFrameVelocity D (B t)) t)
    (hD : D.IsSymm) (hunit : IsUnit (B t)) :
    HasDerivAt (fun s => B s * (B s)ᵀ) D t := by
  simpa only [horizontalFrameVelocity_gram D (B t) hD hunit] using hasDerivAt_frameGram hB

theorem contDiffAt_matrix_inv {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : IsUnit B) :
    ContDiffAt ℝ ⊤ (fun C : Matrix (Fin n) (Fin n) ℝ => C⁻¹) B := by
  obtain ⟨U, rfl⟩ := hB
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using
    (contDiffAt_ringInverse (𝕜 := ℝ) (n := ⊤) U)

theorem contDiffAt_horizontalFrameVelocity {n : ℕ}
    (D B : Matrix (Fin n) (Fin n) ℝ) (hB : IsUnit B) :
    ContDiffAt ℝ ⊤ (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      horizontalFrameVelocity p.1 p.2) (D, B) := by
  have hi := (contDiffAt_matrix_inv B hB).comp (D, B) contDiffAt_snd
  have ht := ((Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toContinuousLinearEquiv.contDiff.contDiffAt).comp (D, B) hi
  exact contDiffAt_const.smul (contDiffAt_fst.mul ht)

end PaperI
