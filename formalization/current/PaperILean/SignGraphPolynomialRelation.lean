import PaperILean.PolynomialSignNeighborhood
import Mathlib.Algebra.MvPolynomial.Degrees

/-! I625-638: algebraic preparation for growth. A single-valued relation with
a finite sign description lies in the zero set of one nonzero polynomial.
No quantifier elimination, graph continuity or root bound is assumed. -/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace PaperI
attribute [local instance] Classical.propDecidable

def polynomialGraphCoordinates {α : Type*} (x : α → ℝ) (t : ℝ) : α ⊕ Unit → ℝ :=
  Sum.elim x (fun _ => t)

theorem continuous_polynomialGraphCoordinates {α : Type*} (x : α → ℝ) :
    Continuous (polynomialGraphCoordinates x) := by
  apply continuous_pi
  intro a
  cases a with
  | inl a => exact continuous_const
  | inr u => exact continuous_id

theorem single_valued_sign_graph_has_zero {α : Type*}
    {A : Finset (MvPolynomial (α ⊕ Unit) ℝ)} {S : Set ((α ⊕ Unit) → ℝ)}
    (hS : PolynomialSignDetermined A S)
    (hu : ∀ (x : α → ℝ) (t u : ℝ), polynomialGraphCoordinates x t ∈ S →
      polynomialGraphCoordinates x u ∈ S → t = u)
    (x : α → ℝ) (t : ℝ) (hx : polynomialGraphCoordinates x t ∈ S) :
    ∃ p ∈ A, p ≠ 0 ∧ MvPolynomial.eval (polynomialGraphCoordinates x t) p = 0 := by
  by_contra h
  have hnz : ∀ p ∈ A, p ≠ 0 →
      MvPolynomial.eval (polynomialGraphCoordinates x t) p ≠ 0 := by
    intro p hp hp0 he
    exact h ⟨p, hp, hp0, he⟩
  have he := polynomialSignDetermined_eventually_membership hS
    (continuous_polynomialGraphCoordinates x).continuousAt hnz
  have hm : ∀ᶠ u in 𝓝[>] t, polynomialGraphCoordinates x u ∈ S :=
    (he.mono (fun _ hy => hy.mp hx)).filter_mono nhdsWithin_le_nhds
  have ht : ∀ᶠ u in 𝓝[>] t, t < u := self_mem_nhdsWithin
  obtain ⟨u, hmem, hlt⟩ := (hm.and ht).exists
  exact (ne_of_lt hlt) (hu x t u hx hmem)

def nonzeroPolynomialProduct {α : Type*} (A : Finset (MvPolynomial α ℝ)) :
    MvPolynomial α ℝ := ∏ p ∈ A.filter (fun q => q ≠ 0), p

theorem nonzeroPolynomialProduct_ne_zero {α : Type*} (A : Finset (MvPolynomial α ℝ)) :
    nonzeroPolynomialProduct A ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem nonzeroPolynomialProduct_totalDegree_le {α : Type*}
    (A : Finset (MvPolynomial α ℝ)) :
    (nonzeroPolynomialProduct A).totalDegree ≤ ∑ p ∈ A, p.totalDegree := by
  refine (MvPolynomial.totalDegree_finset_prod (A.filter (fun p => p ≠ 0))
    (fun p => p)).trans ?_
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem eval_nonzeroPolynomialProduct_eq_zero {α : Type*}
    {A : Finset (MvPolynomial α ℝ)} {x : α → ℝ}
    (h : ∃ p ∈ A, p ≠ 0 ∧ MvPolynomial.eval x p = 0) :
    MvPolynomial.eval x (nonzeroPolynomialProduct A) = 0 := by
  obtain ⟨p, hp, hp0, he⟩ := h
  simp only [nonzeroPolynomialProduct, map_prod]
  exact Finset.prod_eq_zero_iff.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hp0⟩, he⟩

theorem single_valued_sign_graph_polynomial_relation {α : Type*}
    {S : Set ((α ⊕ Unit) → ℝ)} (hS : HasPolynomialSignDescription S)
    (hu : ∀ (x : α → ℝ) (t u : ℝ), polynomialGraphCoordinates x t ∈ S →
      polynomialGraphCoordinates x u ∈ S → t = u) :
    ∃ q : MvPolynomial (α ⊕ Unit) ℝ, q ≠ 0 ∧
      ∀ (x : α → ℝ) (t : ℝ), polynomialGraphCoordinates x t ∈ S →
        MvPolynomial.eval (polynomialGraphCoordinates x t) q = 0 := by
  obtain ⟨A, hA⟩ := hS
  exact ⟨nonzeroPolynomialProduct A, nonzeroPolynomialProduct_ne_zero A,
    fun x t hx => eval_nonzeroPolynomialProduct_eq_zero
      (single_valued_sign_graph_has_zero hA hu x t hx)⟩

theorem single_valued_sign_graph_polynomial_relation_degree {α : Type*}
    {A : Finset (MvPolynomial (α ⊕ Unit) ℝ)} {S : Set ((α ⊕ Unit) → ℝ)}
    (hS : PolynomialSignDetermined A S)
    (hu : ∀ (x : α → ℝ) (t u : ℝ), polynomialGraphCoordinates x t ∈ S →
      polynomialGraphCoordinates x u ∈ S → t = u) :
    ∃ q : MvPolynomial (α ⊕ Unit) ℝ, q ≠ 0 ∧
      q.totalDegree ≤ ∑ p ∈ A, p.totalDegree ∧
      ∀ (x : α → ℝ) (t : ℝ), polynomialGraphCoordinates x t ∈ S →
        MvPolynomial.eval (polynomialGraphCoordinates x t) q = 0 := by
  exact ⟨nonzeroPolynomialProduct A, nonzeroPolynomialProduct_ne_zero A,
    nonzeroPolynomialProduct_totalDegree_le A,
    fun x t hx => eval_nonzeroPolynomialProduct_eq_zero
      (single_valued_sign_graph_has_zero hS hu x t hx)⟩

end PaperI
