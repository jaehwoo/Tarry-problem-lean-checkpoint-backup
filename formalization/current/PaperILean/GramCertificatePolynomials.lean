import PaperILean.OrderedGramMatrixCertificate
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Explicit polynomial equations for the certificate at I600/I693.
The matrix entries, singular values and orthogonal witness are all real
coordinates. This is an algebraic encoding, not quantifier elimination. -/
noncomputable section
open scoped Matrix BigOperators
namespace PaperI
variable {m : Type*} [Fintype m] {n : ℕ}

abbrev GramCertificateVariable (m : Type*) (n : ℕ) :=
  (m × Fin n) ⊕ (Fin n ⊕ (Fin n × Fin n))

def gramCertificateCoordinates (A : Matrix m (Fin n) ℝ) (s : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : GramCertificateVariable m n → ℝ :=
  Sum.elim (fun ri => A ri.1 ri.2) (Sum.elim s (fun ij => Q ij.1 ij.2))

def gramOrthogonalityPolynomial (m : Type*) [Fintype m] (n : ℕ) (i j : Fin n) :
    MvPolynomial (GramCertificateVariable m n) ℝ :=
  (∑ l : Fin n, MvPolynomial.X (.inr (.inr (l, i))) *
    MvPolynomial.X (.inr (.inr (l, j)))) - MvPolynomial.C (if i = j then 1 else 0)

def gramDiagonalPolynomial (m : Type*) [Fintype m] (n : ℕ) (i j : Fin n) :
    MvPolynomial (GramCertificateVariable m n) ℝ :=
  (∑ q : Fin n, (∑ p : Fin n, MvPolynomial.X (.inr (.inr (p, i))) *
    (∑ r : m, MvPolynomial.X (.inl (r, p)) * MvPolynomial.X (.inl (r, q)))) *
      MvPolynomial.X (.inr (.inr (q, j)))) -
    (if i = j then MvPolynomial.X (.inr (.inl i)) ^ 2 else 0)

theorem eval_gramOrthogonalityPolynomial (A : Matrix m (Fin n) ℝ) (s : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MvPolynomial.eval (gramCertificateCoordinates A s Q) (gramOrthogonalityPolynomial m n i j) =
      (Qᵀ * Q) i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  simp [gramOrthogonalityPolynomial, gramCertificateCoordinates, MvPolynomial.eval_sum,
    Matrix.mul_apply, Matrix.one_apply]

theorem eval_gramDiagonalPolynomial (A : Matrix m (Fin n) ℝ) (s : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MvPolynomial.eval (gramCertificateCoordinates A s Q) (gramDiagonalPolynomial m n i j) =
      (Qᵀ * (Aᵀ * A) * Q) i j - (Matrix.diagonal (fun i => s i ^ 2)) i j := by
  classical
  by_cases hij : i = j <;> simp [gramDiagonalPolynomial, gramCertificateCoordinates,
    MvPolynomial.eval_sum, Matrix.mul_apply, Matrix.diagonal_apply, hij]

theorem gramOrthogonalityPolynomial_degree (m : Type*) [Fintype m]
    (n : ℕ) (i j : Fin n) : (gramOrthogonalityPolynomial m n i j).totalDegree ≤ 2 := by
  unfold gramOrthogonalityPolynomial
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro l hl
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · rw [MvPolynomial.totalDegree_C]
    omega

theorem gramDiagonalPolynomial_degree (m : Type*) [Fintype m]
    (n : ℕ) (i j : Fin n) : (gramDiagonalPolynomial m n i j).totalDegree ≤ 4 := by
  classical
  unfold gramDiagonalPolynomial
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro q hq
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have h3 : (∑ p : Fin n, (MvPolynomial.X (.inr (.inr (p, i))) :
        MvPolynomial (GramCertificateVariable m n) ℝ) *
        (∑ r : m, MvPolynomial.X (.inl (r, p)) * MvPolynomial.X (.inl (r, q)))).totalDegree ≤ 3 := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro p hp
      apply (MvPolynomial.totalDegree_mul _ _).trans
      have h2 : (∑ r : m, (MvPolynomial.X (.inl (r, p)) :
          MvPolynomial (GramCertificateVariable m n) ℝ) * (MvPolynomial.X (.inl (r, q)) : MvPolynomial (GramCertificateVariable m n) ℝ)).totalDegree ≤ 2 := by
        apply MvPolynomial.totalDegree_finsetSum_le
        intro r hr
        exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
      simpa using Nat.add_le_add_left h2 1
    simpa using Nat.add_le_add_right h3 1
  · split <;> simp [MvPolynomial.totalDegree_X_pow]

theorem orderedGramCertificate_iff_polynomial_equations (A : Matrix m (Fin n) ℝ)
    (s : Fin n → ℝ) :
    OrderedGramCertificate A s ↔
      (∀ i, 0 ≤ s i) ∧ (∀ i j : Fin n, i ≤ j → s j ≤ s i) ∧
        ∃ Q : Matrix (Fin n) (Fin n) ℝ,
          (∀ i j, MvPolynomial.eval (gramCertificateCoordinates A s Q)
            (gramOrthogonalityPolynomial m n i j) = 0) ∧
          (∀ i j, MvPolynomial.eval (gramCertificateCoordinates A s Q)
            (gramDiagonalPolynomial m n i j) = 0) := by
  simp only [eval_gramOrthogonalityPolynomial, eval_gramDiagonalPolynomial, sub_eq_zero]
  constructor
  · rintro ⟨hn, ho, Q, hQ, hD⟩
    exact ⟨hn, fun i j h => ho h, Q, fun i j => congrFun (congrFun hQ i) j,
      fun i j => congrFun (congrFun hD i) j⟩
  · rintro ⟨hn, ho, Q, hQ, hD⟩
    exact ⟨hn, fun {i j} h => ho i j h, Q, Matrix.ext hQ, Matrix.ext hD⟩

theorem descendingSingularValues_polynomial_graph (A : Matrix m (Fin n) ℝ)
    (s : Fin n → ℝ) :
    s = descendingSingularValues A ↔
      (∀ i, 0 ≤ s i) ∧ (∀ i j : Fin n, i ≤ j → s j ≤ s i) ∧
        ∃ Q : Matrix (Fin n) (Fin n) ℝ,
          (∀ i j, MvPolynomial.eval (gramCertificateCoordinates A s Q)
            (gramOrthogonalityPolynomial m n i j) = 0) ∧
          (∀ i j, MvPolynomial.eval (gramCertificateCoordinates A s Q)
            (gramDiagonalPolynomial m n i j) = 0) :=
  (orderedGramCertificate_iff A s).symm.trans
    (orderedGramCertificate_iff_polynomial_equations A s)

end PaperI
