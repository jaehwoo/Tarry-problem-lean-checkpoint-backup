import PaperILean.PolynomialSignPullback
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Explicit cardinality and total-degree bounds for polynomial pullback.
There is no finite-dimensional hypothesis and no exclusion of zero degree,
zero polynomials, repeated images, or cancellation. -/

noncomputable section
namespace PaperI
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
attribute [local instance 2000] Classical.typeDecidableEq

theorem polynomial_bind_totalDegree_le {α β : Type*}
    (q : α → MvPolynomial β ℝ) (E : ℕ)
    (hq : ∀ i, (q i).totalDegree ≤ E) (p : MvPolynomial α ℝ) :
    (MvPolynomial.bind₁ q p).totalDegree ≤ p.totalDegree * E := by
  change (MvPolynomial.eval₂ MvPolynomial.C q p).totalDegree ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  calc
    (MvPolynomial.C (p.coeff d) * ∏ i ∈ d.support, q i ^ d i).totalDegree
        ≤ (MvPolynomial.C (p.coeff d)).totalDegree +
          (∏ i ∈ d.support, q i ^ d i).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (∏ i ∈ d.support, q i ^ d i).totalDegree := by simp
    _ ≤ ∑ i ∈ d.support, (q i ^ d i).totalDegree :=
      MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ i ∈ d.support, d i * E := Finset.sum_le_sum fun i _ =>
      (MvPolynomial.totalDegree_pow (q i) (d i)).trans (Nat.mul_le_mul_left (d i) (hq i))
    _ = (∑ i ∈ d.support, d i) * E := (Finset.sum_mul ..).symm
    _ ≤ p.totalDegree * E := Nat.mul_le_mul_right E (MvPolynomial.le_totalDegree hd)

theorem polynomial_sign_pullback_card_degree {α β : Type*}
    (A : Finset (MvPolynomial α ℝ)) (s D E : ℕ)
    (hcard : A.card ≤ s) (hdeg : ∀ p ∈ A, p.totalDegree ≤ D)
    (q : α → MvPolynomial β ℝ) (hq : ∀ i, (q i).totalDegree ≤ E) :
    (A.image (MvPolynomial.bind₁ q)).card ≤ s ∧
      ∀ p ∈ A.image (MvPolynomial.bind₁ q), p.totalDegree ≤ D * E := by
  refine ⟨Finset.card_image_le.trans hcard, ?_⟩
  intro p hp
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
  exact (polynomial_bind_totalDegree_le q E hq a).trans
    (Nat.mul_le_mul_right E (hdeg a ha))

theorem polynomial_preimage_bounded_sign_format {α β : Type*}
    (A : Finset (MvPolynomial α ℝ)) (S : Set (α → ℝ)) (s D E : ℕ)
    (hcard : A.card ≤ s) (hdeg : ∀ p ∈ A, p.totalDegree ≤ D)
    (hS : PolynomialSignDetermined A S)
    (q : α → MvPolynomial β ℝ) (hq : ∀ i, (q i).totalDegree ≤ E) :
    ∃ B : Finset (MvPolynomial β ℝ), B.card ≤ s ∧
      (∀ p ∈ B, p.totalDegree ≤ D * E) ∧
      PolynomialSignDetermined B
        {x : β → ℝ | (fun i => MvPolynomial.eval x (q i)) ∈ S} := by
  have hb := polynomial_sign_pullback_card_degree A s D E hcard hdeg q hq
  refine ⟨_,hb.1,hb.2,?_⟩
  intro x y hxy
  apply hS
  intro p hp
  have h := hxy (MvPolynomial.bind₁ q p) (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  simpa only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁] using h

end PaperI
