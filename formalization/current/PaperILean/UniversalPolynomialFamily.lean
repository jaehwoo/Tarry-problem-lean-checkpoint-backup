import PaperILean.PolynomialSignDefinability
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Fintype.Pi

/-! A fixed finite coefficient space for all polynomials of bounded total degree.
The exponent box is allowed to contain extra monomials: their coefficients are
zero for the polynomial being represented. No nonzero coefficient is assumed. -/

noncomputable section
open scoped BigOperators
namespace PaperI
attribute [local instance] Classical.propDecidable

def boxedExponent {α : Type*} [Fintype α] (D : ℕ)
    (m : α → Fin (D + 1)) : α →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (m i).val)

@[simp] theorem boxedExponent_apply {α : Type*} [Fintype α] (D : ℕ)
    (m : α → Fin (D + 1)) (i : α) : boxedExponent D m i = (m i).val := by
  simp [boxedExponent]

theorem boxedExponent_injective {α : Type*} [Fintype α] (D : ℕ) :
    Function.Injective (boxedExponent (α := α) D) := by
  intro m n h
  funext i
  apply Fin.ext
  simpa only [boxedExponent_apply] using congrArg (fun f : α →₀ ℕ => f i) h

def boxedExponents (α : Type*) [Fintype α] (D : ℕ) : Finset (α →₀ ℕ) :=
  Finset.univ.map ⟨boxedExponent D, boxedExponent_injective D⟩

theorem support_subset_boxedExponents {α : Type*} [Fintype α]
    (p : MvPolynomial α ℝ) (D : ℕ) (hp : p.totalDegree ≤ D) :
    p.support ⊆ boxedExponents α D := by
  classical
  intro m hm
  let b : α → Fin (D + 1) := fun i =>
    ⟨m i, Nat.lt_succ_of_le (((MvPolynomial.monomial_le_degreeOf i hm).trans
      (p.degreeOf_le_totalDegree i)).trans hp)⟩
  change m ∈ Finset.univ.map ⟨boxedExponent D, boxedExponent_injective D⟩
  apply Finset.mem_map.mpr
  refine ⟨b, Finset.mem_univ _, ?_⟩
  ext i
  simp [b]

theorem eval_eq_boxed_sum {α : Type*} [Fintype α]
    (p : MvPolynomial α ℝ) (D : ℕ) (hp : p.totalDegree ≤ D) (x : α → ℝ) :
    MvPolynomial.eval x p =
      ∑ m : α → Fin (D + 1), p.coeff (boxedExponent D m) * ∏ i, x i ^ (m i).val := by
  classical
  rw [MvPolynomial.eval_eq']
  calc
    ∑ m ∈ p.support, p.coeff m * ∏ i, x i ^ m i =
        ∑ m ∈ boxedExponents α D, p.coeff m * ∏ i, x i ^ m i := by
      apply Finset.sum_subset (support_subset_boxedExponents p D hp)
      intro m _ hm
      simp only [MvPolynomial.mem_support_iff, not_not] at hm
      simp [hm]
    _ = _ := by simp [boxedExponents]

def universalCoefficientPolynomial (α : Type*) [Fintype α] (s D : ℕ) (i : Fin s) :
    MvPolynomial ((Fin s × (α → Fin (D + 1))) ⊕ α) ℝ :=
  ∑ m : α → Fin (D + 1), MvPolynomial.X (Sum.inl (i, m)) *
    ∏ j : α, MvPolynomial.X (Sum.inr j) ^ (m j).val

def polynomialFamilyCoefficients {α : Type*} [Fintype α] {s : ℕ}
    (D : ℕ) (p : Fin s → MvPolynomial α ℝ) :
    (Fin s × (α → Fin (D + 1))) → ℝ :=
  fun a => (p a.1).coeff (boxedExponent D a.2)

theorem universalCoefficientPolynomial_eval {α : Type*} [Fintype α]
    (s D : ℕ) (p : Fin s → MvPolynomial α ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ D) (x : α → ℝ) (i : Fin s) :
    MvPolynomial.eval (Sum.elim (polynomialFamilyCoefficients D p) x)
      (universalCoefficientPolynomial α s D i) = MvPolynomial.eval x (p i) := by
  simp only [universalCoefficientPolynomial, map_sum, map_mul, map_prod, map_pow,
    MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr, polynomialFamilyCoefficients]
  exact (eval_eq_boxed_sum (p i) D (hp i) x).symm

end PaperI
