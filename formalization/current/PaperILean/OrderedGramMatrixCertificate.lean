import PaperILean.OrderedGramBasisCertificate

/-! I600 and I668--694: exact finite real matrix certificate for the ordered
singular-value graph. No simple-spectrum or full-rank hypothesis is added. -/

noncomputable section
open scoped Matrix InnerProductSpace
namespace PaperI
variable {m : Type*} [Fintype m] {n : ℕ}

def orthonormalColumnMatrix
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => b j i

theorem orthonormalColumnMatrix_orthogonal
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    (orthonormalColumnMatrix b)ᵀ * orthonormalColumnMatrix b = 1 := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_conjTranspose_mul_self b

theorem gram_mul_orthonormalColumnMatrix (A : Matrix m (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (s : Fin n → ℝ)
    (heig : ∀ i, Matrix.toEuclideanLin (Aᵀ * A) (b i) = s i ^ 2 • b i) :
    (Aᵀ * A) * orthonormalColumnMatrix b =
      orthonormalColumnMatrix b * Matrix.diagonal (fun i => s i ^ 2) := by
  ext i j
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) (heig j)
  rw [Matrix.mul_diagonal]
  change ((Aᵀ * A) *ᵥ (fun x => b j x)) i = b j i * s j ^ 2
  simpa only [Matrix.toEuclideanLin_apply, PiLp.smul_apply, smul_eq_mul, mul_comm] using h

theorem orthonormalColumnMatrix_gram_diagonal (A : Matrix m (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (s : Fin n → ℝ)
    (heig : ∀ i, Matrix.toEuclideanLin (Aᵀ * A) (b i) = s i ^ 2 • b i) :
    (orthonormalColumnMatrix b)ᵀ * (Aᵀ * A) * orthonormalColumnMatrix b =
      Matrix.diagonal (fun i => s i ^ 2) := by
  rw [Matrix.mul_assoc, gram_mul_orthonormalColumnMatrix A b s heig,
    ← Matrix.mul_assoc, orthonormalColumnMatrix_orthogonal, Matrix.one_mul]

theorem orthogonal_matrix_columns (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) :
    Orthonormal ℝ (fun j => ((WithLp.equiv 2 (Fin n → ℝ)).symm (Qᵀ j) : EuclideanSpace ℝ (Fin n))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrFun (congrFun hQ i) j
  simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply,
    Matrix.one_apply, dotProduct, Matrix.transpose_apply, mul_comm] using h

def orthogonalMatrixBasis (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  OrthonormalBasis.mk (orthogonal_matrix_columns Q hQ)
    ((orthogonal_matrix_columns Q hQ).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simp)).ge

theorem orthogonalMatrixBasis_apply (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) (j : Fin n) :
    orthogonalMatrixBasis Q hQ j = (WithLp.equiv 2 (Fin n → ℝ)).symm (Qᵀ j) := by
  simp [orthogonalMatrixBasis]

theorem orthogonalMatrixBasis_gram_apply (A : Matrix m (Fin n) ℝ)
    (s : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1)
    (hD : Qᵀ * (Aᵀ * A) * Q = Matrix.diagonal (fun i => s i ^ 2)) (j : Fin n) :
    Matrix.toEuclideanLin (Aᵀ * A) (orthogonalMatrixBasis Q hQ j) =
      s j ^ 2 • orthogonalMatrixBasis Q hQ j := by
  have hQQ : Q * Qᵀ = 1 := Matrix.mul_eq_one_comm.mp hQ
  have hG : (Aᵀ * A) * Q = Q * Matrix.diagonal (fun i => s i ^ 2) := by
    rw [← hD]
    simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  rw [orthogonalMatrixBasis_apply]
  apply PiLp.ext
  intro i
  have h := congrFun (congrFun hG i) j
  rw [Matrix.mul_diagonal] at h
  change ((Aᵀ * A) *ᵥ (Qᵀ j)) i = s j ^ 2 * Q i j
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using h

/-- Only scalar order, finite real matrix equations, and an existential matrix occur. -/
def OrderedGramCertificate (A : Matrix m (Fin n) ℝ) (s : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ s i) ∧ Antitone s ∧
    ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      Qᵀ * Q = 1 ∧ Qᵀ * (Aᵀ * A) * Q = Matrix.diagonal (fun i => s i ^ 2)

theorem orderedGramCertificate_iff (A : Matrix m (Fin n) ℝ) (s : Fin n → ℝ) :
    OrderedGramCertificate A s ↔ s = descendingSingularValues A := by
  constructor
  · rintro ⟨hn, ho, Q, hQ, hD⟩
    exact ordered_gram_basis_unique A (orthogonalMatrixBasis Q hQ) s hn ho
      (orthogonalMatrixBasis_gram_apply A s Q hQ hD)
  · rintro rfl
    exact ⟨descendingSingularValues_nonneg A, descendingSingularValues_antitone A,
      orthonormalColumnMatrix (orderedSingularBasis A),
      orthonormalColumnMatrix_orthogonal _,
      orthonormalColumnMatrix_gram_diagonal A _ _ (orderedSingularBasis_gram_apply A)⟩

theorem descendingSingularValue_graph_iff (A : Matrix m (Fin n) ℝ)
    (i : Fin n) (t : ℝ) :
    t = descendingSingularValues A i ↔
      ∃ s : Fin n → ℝ, OrderedGramCertificate A s ∧ s i = t := by
  constructor
  · intro h
    exact ⟨descendingSingularValues A, (orderedGramCertificate_iff A _).mpr rfl, h.symm⟩
  · rintro ⟨s, hs, hi⟩
    rw [(orderedGramCertificate_iff A s).mp hs] at hi
    exact hi.symm

end PaperI
