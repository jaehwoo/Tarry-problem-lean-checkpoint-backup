import PaperILean.PolynomialSignDescription
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Fintype.EquivFin

/-! A finite collection of at most `s` degree-bounded polynomials can be
enumerated by `Fin s`, padding unused positions with zero. This preserves
the existing polynomial-sign definition of a set; it does not redefine
manuscript format or claim an elimination-format bound. -/

noncomputable section
namespace PaperI
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def paddedPolynomialTuple {α : Type*} (A : Finset (MvPolynomial α ℝ))
    (s : ℕ) (i : Fin s) : MvPolynomial α ℝ :=
  if h : i.val < A.card then (A.equivFin.symm ⟨i.val, h⟩).val else 0

theorem paddedPolynomialTuple_eq_zero {α : Type*}
    (A : Finset (MvPolynomial α ℝ)) (s : ℕ) (i : Fin s)
    (h : A.card ≤ i.val) : paddedPolynomialTuple A s i = 0 := by
  simp [paddedPolynomialTuple, Nat.not_lt.mpr h]

theorem subset_image_paddedPolynomialTuple {α : Type*}
    (A : Finset (MvPolynomial α ℝ)) (s : ℕ) (hcard : A.card ≤ s) :
    A ⊆ Finset.univ.image (paddedPolynomialTuple A s) := by
  intro q hq
  let j := A.equivFin ⟨q, hq⟩
  let i : Fin s := ⟨j.val, lt_of_lt_of_le j.isLt hcard⟩
  refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
  change (if h : j.val < A.card then (A.equivFin.symm ⟨j.val, h⟩).val else 0) = q
  rw [dif_pos j.isLt]
  exact congrArg Subtype.val (A.equivFin.symm_apply_apply ⟨q, hq⟩)

theorem paddedPolynomialTuple_totalDegree_le {α : Type*}
    (A : Finset (MvPolynomial α ℝ)) (s D : ℕ)
    (hdegree : ∀ q ∈ A, q.totalDegree ≤ D) (i : Fin s) :
    (paddedPolynomialTuple A s i).totalDegree ≤ D := by
  unfold paddedPolynomialTuple
  split
  · exact hdegree _ (A.equivFin.symm _).property
  · simp

theorem exists_bounded_polynomial_tuple_of_signDetermined {α : Type*}
    (A : Finset (MvPolynomial α ℝ)) (S : Set (α → ℝ)) (s D : ℕ)
    (hcard : A.card ≤ s) (hdegree : ∀ q ∈ A, q.totalDegree ≤ D)
    (hS : PolynomialSignDetermined A S) :
    ∃ p : Fin s → MvPolynomial α ℝ,
      (∀ i, (p i).totalDegree ≤ D) ∧ PolynomialSignDetermined (Finset.univ.image p) S := by
  refine ⟨paddedPolynomialTuple A s, paddedPolynomialTuple_totalDegree_le A s D hdegree, ?_⟩
  exact polynomialSignDetermined_mono hS (subset_image_paddedPolynomialTuple A s hcard)

end PaperI
