import PaperILean.TensorOrthogonalInvariance

/-! The actual first-slot contraction Gram matrix in Paper I229-232.
The tensor has order n+1, so contraction has order n. All ordered components
are retained. The construction applies also to nonsymmetric tensors; only the
later factor (n+1) in frame variation will require tensor symmetry. -/
noncomputable section
open scoped BigOperators Matrix
namespace PaperI

def tensorContractionMatrix {n : ℕ} (T : TensorSpace (n + 1)) :
    Matrix (Fin n → Fin 3) (Fin 3) ℝ :=
  fun a i => tensorCoordinates T (Fin.cons i a)

def tensorContractionGram {n : ℕ} (T : TensorSpace (n + 1)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (tensorContractionMatrix T)ᵀ * tensorContractionMatrix T

theorem tensorContractionGram_apply {n : ℕ} (T : TensorSpace (n + 1)) (i j : Fin 3) :
    tensorContractionGram T i j =
      ∑ a : Fin n → Fin 3, tensorCoordinates T (Fin.cons i a) * tensorCoordinates T (Fin.cons j a) := by
  rfl

theorem tensorContractionGram_posSemidef {n : ℕ} (T : TensorSpace (n + 1)) :
    (tensorContractionGram T).PosSemidef := by
  simpa only [tensorContractionGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (tensorContractionMatrix T)

theorem tensorContractionGram_isSymm {n : ℕ} (T : TensorSpace (n + 1)) :
    (tensorContractionGram T).IsSymm := by
  unfold tensorContractionGram
  simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem tensorContractionMatrix_mulVec {n : ℕ} (T : TensorSpace (n + 1)) (u : PhysicalSpace) :
    tensorContractionMatrix T *ᵥ u = tensorCoordinates (T.curryLeft u) := by
  funext a
  rw [tensor_curryLeft_coordinates]
  simp only [Matrix.mulVec, dotProduct, tensorContractionMatrix, mul_comm]

theorem tensorContractionGram_quadratic {n : ℕ} (T : TensorSpace (n + 1)) (u : PhysicalSpace) :
    u ⬝ᵥ (tensorContractionGram T *ᵥ u) = (tensorHSNorm (T.curryLeft u)) ^ 2 := by
  unfold tensorContractionGram
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    tensorContractionMatrix_mulVec, tensorHSNorm_sq]
  simp only [dotProduct, pow_two]

theorem tensorContractionGram_trace {n : ℕ} (T : TensorSpace (n + 1)) :
    Matrix.trace (tensorContractionGram T) = (tensorHSNorm T) ^ 2 := by
  rw [tensorHSNorm_sq_split]
  simp only [Matrix.trace, Matrix.diag_apply, tensorContractionGram_apply, ← pow_two]
  rw [Finset.sum_comm]

theorem tensorContractionGram_zero (n : ℕ) :
    tensorContractionGram (0 : TensorSpace (n + 1)) = 0 := by
  ext i j
  simp [tensorContractionGram_apply, tensorCoordinates]

theorem affineJetTensor_mem_symmetricTensor {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) :
    affineJetTensor F c B r ∈ symmetricTensorSubmodule r := by
  intro v σ
  simp only [affineJetTensor_apply, Function.comp_apply]
  exact iteratedFDeriv_phase_perm F r c (fun j => B *ᵥ v j) σ

end PaperI
