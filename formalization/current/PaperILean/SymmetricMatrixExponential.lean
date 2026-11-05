import PaperILean.DiagonalExponentialDifferential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! The real symmetric normed domain supplied by Paper I214-223.
The exponential derivative is restricted to this actual subspace. Its inverse
at a positive diagonal point is the actual symmetric-space CFC-log derivative,
including collisions, by the inverse-function theorem and log(exp X)=X.
This alternative route does not assume the Lewis-Sendov spectral Hessian.
-/

noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm Topology
namespace PaperI

set_option maxHeartbeats 30000

def symmetricMatrixSubmodule (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | A.IsSymm}
  zero_mem' := by show (0 : Matrix (Fin n) (Fin n) ℝ)ᵀ = 0; simp
  add_mem' := fun hA hB => hA.add hB
  smul_mem' := fun r _ hA => hA.smul r

abbrev SymmetricMatrix (n : ℕ) := symmetricMatrixSubmodule n

instance symmetricMatrix_completeSpace (n : ℕ) : CompleteSpace (SymmetricMatrix n) :=
  FiniteDimensional.complete ℝ (SymmetricMatrix n)

def symmetricMatrixOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    SymmetricMatrix n := ⟨A, hA⟩

def symmetricMatrixDiagonal {n : ℕ} (a : Fin n → ℝ) : SymmetricMatrix n :=
  symmetricMatrixOf (Matrix.diagonal a) (Matrix.isSymm_diagonal a)

def symmetricMatrixIncl (n : ℕ) :
    SymmetricMatrix n →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (symmetricMatrixSubmodule n).subtypeL

def symmetricMatrixProjectionLinear (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] SymmetricMatrix n :=
  LinearMap.codRestrict (symmetricMatrixSubmodule n)
    ((1 / 2 : ℝ) • ((LinearMap.id : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ) +
      (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap))
    (by
      intro A
      change ((1 / 2 : ℝ) • (A + Aᵀ)).IsSymm
      show ((1 / 2 : ℝ) • (A + Aᵀ))ᵀ = (1 / 2 : ℝ) • (A + Aᵀ)
      simp [Matrix.transpose_smul, Matrix.transpose_add, add_comm])

def symmetricMatrixProjection (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] SymmetricMatrix n :=
  LinearMap.toContinuousLinearMap (symmetricMatrixProjectionLinear n)

theorem symmetricMatrixProjection_of_symm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    symmetricMatrixProjection n A = symmetricMatrixOf A hA := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (A + Aᵀ) = A
  rw [hA]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem symmetricMatrixProjection_incl {n : ℕ} (A : SymmetricMatrix n) :
    symmetricMatrixProjection n (symmetricMatrixIncl n A) = A :=
  symmetricMatrixProjection_of_symm (A : Matrix (Fin n) (Fin n) ℝ) A.property

def symmetricMatrixExp {n : ℕ} (X : SymmetricMatrix n) : SymmetricMatrix n :=
  symmetricMatrixOf (NormedSpace.exp ℝ (X : Matrix (Fin n) (Fin n) ℝ)) (X.property.exp ℝ)

def symmetricMatrixLog {n : ℕ} (A : SymmetricMatrix n) : SymmetricMatrix n :=
  symmetricMatrixOf (CFC.log (A : Matrix (Fin n) (Fin n) ℝ))
    ((realMatrix_isSelfAdjoint_iff_isSymm _).mp
      (IsSelfAdjoint.log (a := (A : Matrix (Fin n) (Fin n) ℝ))))

theorem symmetricMatrixProjection_exp {n : ℕ} (X : SymmetricMatrix n) :
    symmetricMatrixProjection n (NormedSpace.exp ℝ (symmetricMatrixIncl n X)) =
      symmetricMatrixExp X :=
  symmetricMatrixProjection_of_symm _ (X.property.exp ℝ)

theorem symmetricMatrixLog_exp {n : ℕ} (X : SymmetricMatrix n) :
    symmetricMatrixLog (symmetricMatrixExp X) = X := by
  apply Subtype.ext
  change CFC.log (NormedSpace.exp ℝ (X : Matrix (Fin n) (Fin n) ℝ)) =
    (X : Matrix (Fin n) (Fin n) ℝ)
  exact CFC.log_exp (X : Matrix (Fin n) (Fin n) ℝ)
    ((realMatrix_isSelfAdjoint_iff_isSymm _).mpr X.property)

theorem symmetricMatrixExp_posDef {n : ℕ} (X : SymmetricMatrix n) :
    (symmetricMatrixExp X : Matrix (Fin n) (Fin n) ℝ).PosDef :=
  symmetric_matrix_exp_posDef (X : Matrix (Fin n) (Fin n) ℝ) X.property

theorem symmetricMatrixExp_log {n : ℕ} (A : SymmetricMatrix n)
    (hA : (A : Matrix (Fin n) (Fin n) ℝ).PosDef) :
    symmetricMatrixExp (symmetricMatrixLog A) = A := by
  apply Subtype.ext
  exact sourceMatrix_exp_log (A : Matrix (Fin n) (Fin n) ℝ) hA

theorem symmetricMatrixExp_diagonal {n : ℕ} (a : Fin n → ℝ) :
    symmetricMatrixExp (symmetricMatrixDiagonal a) =
      symmetricMatrixDiagonal (fun i => Real.exp (a i)) := by
  apply Subtype.ext
  exact matrix_exp_diagonal_real a

theorem diagonalExpDifferential_isSymm {n : ℕ} (a : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (hV : V.IsSymm) :
    (diagonalExpDifferential a V).IsSymm := by
  show (diagonalExpDifferential a V)ᵀ = diagonalExpDifferential a V
  ext i j
  simp only [Matrix.transpose_apply, diagonalExpDifferential_apply]
  rw [hV.apply i j, expDividedDifference_symm (a j) (a i)]

theorem diagonalExpDifferentialEquiv_symm_isSymm {n : ℕ} (a : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (hV : V.IsSymm) :
    ((diagonalExpDifferentialEquiv a).symm V).IsSymm := by
  show ((diagonalExpDifferentialEquiv a).symm V)ᵀ =
    (diagonalExpDifferentialEquiv a).symm V
  ext i j
  simp only [Matrix.transpose_apply, diagonalExpDifferentialEquiv_symm_apply]
  rw [hV.apply i j, expDividedDifference_symm (a j) (a i)]

def symmetricDiagonalExpDifferentialEquiv {n : ℕ} (a : Fin n → ℝ) :
    SymmetricMatrix n ≃L[ℝ] SymmetricMatrix n :=
  (LinearEquiv.toContinuousLinearEquiv {
    toFun := fun V => symmetricMatrixOf (diagonalExpDifferentialEquiv a V)
      (diagonalExpDifferential_isSymm a V V.property)
    invFun := fun V => symmetricMatrixOf ((diagonalExpDifferentialEquiv a).symm V)
      (diagonalExpDifferentialEquiv_symm_isSymm a V V.property)
    map_add' := by intro V W; apply Subtype.ext; exact (diagonalExpDifferentialEquiv a).map_add _ _
    map_smul' := by intro r V; apply Subtype.ext; exact (diagonalExpDifferentialEquiv a).map_smul _ _
    left_inv := by intro V; apply Subtype.ext; exact (diagonalExpDifferentialEquiv a).symm_apply_apply _
    right_inv := by intro V; apply Subtype.ext; exact (diagonalExpDifferentialEquiv a).apply_symm_apply _ })

theorem symmetricDiagonalExpDifferentialEquiv_eq_composition {n : ℕ} (a : Fin n → ℝ) :
    (symmetricDiagonalExpDifferentialEquiv a : SymmetricMatrix n →L[ℝ] SymmetricMatrix n) =
      (symmetricMatrixProjection n).comp ((diagonalExpDifferential a).comp (symmetricMatrixIncl n)) := by
  apply ContinuousLinearMap.ext
  intro V
  exact (symmetricMatrixProjection_of_symm _
    (diagonalExpDifferential_isSymm a V V.property)).symm

theorem symmetricMatrixExp_diagonal_hasStrictFDerivAt {n : ℕ} (a : Fin n → ℝ) :
    HasStrictFDerivAt symmetricMatrixExp
      (symmetricDiagonalExpDifferentialEquiv a : SymmetricMatrix n →L[ℝ] SymmetricMatrix n)
      (symmetricMatrixDiagonal a) := by
  have he : HasStrictFDerivAt (NormedSpace.exp ℝ)
      (diagonalExpDifferential a) (Matrix.diagonal a) := by
    rw [← matrixExpDifferential_diagonal]
    exact matrix_exp_hasStrictFDerivAt _
  have hc := he.comp (symmetricMatrixDiagonal a)
    ((symmetricMatrixIncl n).hasStrictFDerivAt)
  have hp := (symmetricMatrixProjection n).hasStrictFDerivAt.comp
    (symmetricMatrixDiagonal a) hc
  rw [symmetricDiagonalExpDifferentialEquiv_eq_composition]
  simpa only [Function.comp_def, symmetricMatrixProjection_exp] using hp

theorem symmetricMatrixLog_diagonal_hasStrictFDerivAt {n : ℕ} (a : Fin n → ℝ) :
    HasStrictFDerivAt symmetricMatrixLog
      ((symmetricDiagonalExpDifferentialEquiv a).symm : SymmetricMatrix n →L[ℝ] SymmetricMatrix n)
      (symmetricMatrixDiagonal (fun i => Real.exp (a i))) := by
  have h := (symmetricMatrixExp_diagonal_hasStrictFDerivAt a).to_local_left_inverse
    (Filter.Eventually.of_forall (fun X => symmetricMatrixLog_exp X))
  simpa only [symmetricMatrixExp_diagonal] using h

def symmetricOrthogonalConjugateLinearEquiv {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ)) : SymmetricMatrix n ≃ₗ[ℝ] SymmetricMatrix n where
  toFun := fun A => symmetricMatrixOf (orthogonalConjugate U (A : Matrix (Fin n) (Fin n) ℝ))
    (orthogonalConjugate_isSymm U (A : Matrix (Fin n) (Fin n) ℝ) A.property)
  invFun := fun A => symmetricMatrixOf (orthogonalConjugate (star U) (A : Matrix (Fin n) (Fin n) ℝ))
    (orthogonalConjugate_isSymm (star U) (A : Matrix (Fin n) (Fin n) ℝ) A.property)
  map_add' := by
    intro A B; apply Subtype.ext
    change orthogonalConjugate U ((A : Matrix (Fin n) (Fin n) ℝ) + B) =
      orthogonalConjugate U A + orthogonalConjugate U B
    simp [orthogonalConjugate, Matrix.add_mul, Matrix.mul_add]
  map_smul' := by
    intro r A; apply Subtype.ext
    exact orthogonalConjugate_smul U r (A : Matrix (Fin n) (Fin n) ℝ)
  left_inv := by
    intro A; apply Subtype.ext
    exact orthogonalConjugate_star_inverse U (A : Matrix (Fin n) (Fin n) ℝ)
  right_inv := by
    intro A; apply Subtype.ext
    simpa only [star_star] using
      orthogonalConjugate_star_inverse (star U) (A : Matrix (Fin n) (Fin n) ℝ)

def symmetricOrthogonalConjugateEquiv {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ)) : SymmetricMatrix n ≃L[ℝ] SymmetricMatrix n :=
  (symmetricOrthogonalConjugateLinearEquiv U).toContinuousLinearEquiv

theorem symmetricOrthogonalConjugate_inverse {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ)) (A : SymmetricMatrix n) :
    symmetricOrthogonalConjugateEquiv U (symmetricOrthogonalConjugateEquiv (star U) A) = A := by
  apply Subtype.ext
  simpa only [star_star] using
    orthogonalConjugate_star_inverse (star U) (A : Matrix (Fin n) (Fin n) ℝ)

theorem symmetricMatrixExp_orthogonalConjugate {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ)) (A : SymmetricMatrix n) :
    symmetricMatrixExp (symmetricOrthogonalConjugateEquiv U A) =
      symmetricOrthogonalConjugateEquiv U (symmetricMatrixExp A) := by
  apply Subtype.ext
  exact matrix_exp_orthogonalConjugate U (A : Matrix (Fin n) (Fin n) ℝ)

def symmetricMatrixExpDifferentialEquiv {n : ℕ} (X : SymmetricMatrix n) :
    SymmetricMatrix n ≃L[ℝ] SymmetricMatrix n :=
  let hX := (realMatrix_isHermitian_iff_isSymm (X : Matrix (Fin n) (Fin n) ℝ)).mpr X.property
  let U := hX.eigenvectorUnitary
  ((symmetricOrthogonalConjugateEquiv (star U)).trans
    (symmetricDiagonalExpDifferentialEquiv hX.eigenvalues)).trans
      (symmetricOrthogonalConjugateEquiv U)

theorem symmetricMatrixExp_hasStrictFDerivAt {n : ℕ} (X : SymmetricMatrix n) :
    HasStrictFDerivAt symmetricMatrixExp
      (symmetricMatrixExpDifferentialEquiv X : SymmetricMatrix n →L[ℝ] SymmetricMatrix n) X := by
  let hX := (realMatrix_isHermitian_iff_isSymm (X : Matrix (Fin n) (Fin n) ℝ)).mpr X.property
  let U := hX.eigenvectorUnitary
  have hx : symmetricOrthogonalConjugateEquiv (star U) X =
      symmetricMatrixDiagonal hX.eigenvalues := by
    apply Subtype.ext
    change star (U : Matrix (Fin n) (Fin n) ℝ) * (X : Matrix (Fin n) (Fin n) ℝ) *
      (U : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal hX.eigenvalues
    simpa [Function.comp_def] using hX.star_mul_self_mul_eq_diagonal
  have hd := symmetricMatrixExp_diagonal_hasStrictFDerivAt hX.eigenvalues
  rw [← hx] at hd
  have h₁ := hd.comp X (symmetricOrthogonalConjugateEquiv (star U)).hasStrictFDerivAt
  have h₂ := (symmetricOrthogonalConjugateEquiv U).hasStrictFDerivAt.comp X h₁
  have hf : (fun Y => symmetricOrthogonalConjugateEquiv U
      (symmetricMatrixExp (symmetricOrthogonalConjugateEquiv (star U) Y))) =
      (symmetricMatrixExp : SymmetricMatrix n → SymmetricMatrix n) := by
    funext Y
    rw [← symmetricMatrixExp_orthogonalConjugate, symmetricOrthogonalConjugate_inverse]
  have h₃ : HasStrictFDerivAt (fun Y => symmetricOrthogonalConjugateEquiv U
      (symmetricMatrixExp (symmetricOrthogonalConjugateEquiv (star U) Y)))
      ((symmetricOrthogonalConjugateEquiv U : SymmetricMatrix n →L[ℝ] SymmetricMatrix n).comp
        ((symmetricDiagonalExpDifferentialEquiv hX.eigenvalues : SymmetricMatrix n →L[ℝ] SymmetricMatrix n).comp
          (symmetricOrthogonalConjugateEquiv (star U) : SymmetricMatrix n →L[ℝ] SymmetricMatrix n))) X := h₂
  rw [hf] at h₃
  exact h₃

theorem symmetricMatrixLog_posDef_hasStrictFDerivAt {n : ℕ} (A : SymmetricMatrix n)
    (hA : (A : Matrix (Fin n) (Fin n) ℝ).PosDef) :
    HasStrictFDerivAt symmetricMatrixLog
      ((symmetricMatrixExpDifferentialEquiv (symmetricMatrixLog A)).symm :
        SymmetricMatrix n →L[ℝ] SymmetricMatrix n) A := by
  have h := (symmetricMatrixExp_hasStrictFDerivAt (symmetricMatrixLog A)).to_local_left_inverse
    (Filter.Eventually.of_forall (fun X => symmetricMatrixLog_exp X))
  simpa only [symmetricMatrixExp_log A hA] using h

theorem symmetricMatrixLog_posDef_hasFDerivAt {n : ℕ} (A : SymmetricMatrix n)
    (hA : (A : Matrix (Fin n) (Fin n) ℝ).PosDef) :
    HasFDerivAt symmetricMatrixLog
      ((symmetricMatrixExpDifferentialEquiv (symmetricMatrixLog A)).symm :
        SymmetricMatrix n →L[ℝ] SymmetricMatrix n) A :=
  (symmetricMatrixLog_posDef_hasStrictFDerivAt A hA).hasFDerivAt

end PaperI
