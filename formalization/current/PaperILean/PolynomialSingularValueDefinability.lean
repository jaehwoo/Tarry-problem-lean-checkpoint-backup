import PaperILean.RealPolynomialDefinability
import PaperILean.GramCertificatePolynomials
import Mathlib.Algebra.MvPolynomial.Monad

/-! Fixed first-order graph definitions for polynomial matrix families.
The witness retains nonnegativity, decreasing order, multiplicities and zeros.
No continuous choice of a diagonalizing matrix or growth theorem is used. -/

noncomputable section
open scoped Matrix BigOperators
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {α m : Type*} [Fintype m] {n : ℕ}

def polynomialGramSubstitution (A : Matrix m (Fin n) (MvPolynomial α ℝ))
    (s : Fin n → MvPolynomial α ℝ) :
    GramCertificateVariable m n → MvPolynomial (α ⊕ (Fin n × Fin n)) ℝ :=
  Sum.elim (fun rj => MvPolynomial.rename Sum.inl (A rj.1 rj.2))
    (Sum.elim (fun i => MvPolynomial.rename Sum.inl (s i))
      (fun ij => MvPolynomial.X (Sum.inr ij)))

omit [Fintype m] in
theorem eval_polynomialGramSubstitution (A : Matrix m (Fin n) (MvPolynomial α ℝ))
    (s : Fin n → MvPolynomial α ℝ) (v : α → ℝ) (q : Fin n × Fin n → ℝ)
    (p : MvPolynomial (GramCertificateVariable m n) ℝ) :
    MvPolynomial.eval (Sum.elim v q) (MvPolynomial.bind₁ (polynomialGramSubstitution A s) p) =
      MvPolynomial.eval (gramCertificateCoordinates (fun r j => MvPolynomial.eval v (A r j))
        (fun i => MvPolynomial.eval v (s i)) (fun i j => q (i, j))) p := by
  simp only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  apply congrArg (fun w : GramCertificateVariable m n → ℝ =>
    MvPolynomial.eval₂Hom (RingHom.id ℝ) w p)
  funext a
  change MvPolynomial.eval (Sum.elim v q) (polynomialGramSubstitution A s a) =
    gramCertificateCoordinates (fun r j => MvPolynomial.eval v (A r j))
      (fun i => MvPolynomial.eval v (s i)) (fun i j => q (i, j)) a
  rcases a with ⟨r, j⟩ | (i | ⟨i, j⟩) <;>
    simp [polynomialGramSubstitution, gramCertificateCoordinates,
      MvPolynomial.eval_rename, Function.comp_def]

theorem polynomialOrderedGramCertificate_definable [Finite α]
    (A : Matrix m (Fin n) (MvPolynomial α ℝ)) (s : Fin n → MvPolynomial α ℝ) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | OrderedGramCertificate (fun r j => MvPolynomial.eval v (A r j))
        (fun i => MvPolynomial.eval v (s i))} := by
  classical
  have hn := realDefinable_finite_all (fun i => realPolynomial_nonneg_definable (s i))
  have ho : (Set.univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | ∀ i j : Fin n, i ≤ j → MvPolynomial.eval v (s j) ≤ MvPolynomial.eval v (s i)} := by
    apply realDefinable_finite_all
    intro i
    apply realDefinable_finite_all
    intro j
    by_cases hij : i ≤ j
    · simpa only [hij, true_implies] using realPolynomial_le_definable (s j) (s i)
    · simpa only [hij, false_implies, Set.setOf_true] using
        (Set.definable_univ :
          (Set.univ : Set ℝ).Definable Language.ring (Set.univ : Set (α → ℝ)))
  let O := fun i j => MvPolynomial.bind₁ (polynomialGramSubstitution A s)
    (gramOrthogonalityPolynomial m n i j)
  let D := fun i j => MvPolynomial.bind₁ (polynomialGramSubstitution A s)
    (gramDiagonalPolynomial m n i j)
  have hO := realDefinable_finite_all (fun i =>
    realDefinable_finite_all (fun j => realPolynomial_zero_definable (O i j)))
  have hD := realDefinable_finite_all (fun i =>
    realDefinable_finite_all (fun j => realPolynomial_zero_definable (D i j)))
  have h := hn.inter (ho.inter (realDefinable_exists (hO.inter hD)))
  convert h using 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, O, D, eval_polynomialGramSubstitution,
    orderedGramCertificate_iff_polynomial_equations]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨Q, hQ, hD⟩
    exact ⟨fun ij => Q ij.1 ij.2, hQ, hD⟩
  · rintro ⟨q, hq, hD⟩
    exact ⟨fun i j => q (i, j), hq, hD⟩

theorem polynomialSingularValueGraph_definable [Finite α]
    (A : Matrix m (Fin n) (MvPolynomial α ℝ)) (t : MvPolynomial α ℝ) (i : Fin n) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | MvPolynomial.eval v t =
        descendingSingularValues (fun r j => MvPolynomial.eval v (A r j)) i} := by
  let B := fun r j => MvPolynomial.rename (Sum.inl : α → α ⊕ Fin n) (A r j)
  let s := fun j : Fin n => (MvPolynomial.X (Sum.inr j) : MvPolynomial (α ⊕ Fin n) ℝ)
  have hg := polynomialOrderedGramCertificate_definable B s
  have he := realPolynomial_zero_definable
    (s i - MvPolynomial.rename Sum.inl t)
  have h := realDefinable_exists (hg.inter he)
  convert h using 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, B, s, map_sub,
    MvPolynomial.eval_rename, MvPolynomial.eval_X, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, sub_eq_zero]
  exact descendingSingularValue_graph_iff _ _ _

end PaperI
