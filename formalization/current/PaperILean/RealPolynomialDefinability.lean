import Mathlib.ModelTheory.Algebra.Ring.Definability
import Mathlib.Data.Real.Sqrt

/-! A standard mathlib first-order interface for real polynomial predicates.
Order is expressed in the ring language using real squares. Definability is
not quantifier elimination, a growth bound, or a claim of effective complexity. -/

noncomputable section
open scoped BigOperators
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem realPolynomial_zero_definable {α : Type*} (p : MvPolynomial α ℝ) :
    (Set.univ : Set ℝ).Definable Language.ring {v : α → ℝ | MvPolynomial.eval v p = 0} := by
  classical
  have h := (FirstOrder.Ring.mvPolynomial_zeroLocus_definable ({p} : Finset _)).mono
    (Set.subset_univ _)
  simpa [MvPolynomial.zeroLocus_span] using h

theorem realDefinable_exists {α β : Type*} [Finite α] [Finite β]
    {s : Set ((α ⊕ β) → ℝ)}
    (hs : (Set.univ : Set ℝ).Definable Language.ring s) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | ∃ w : β → ℝ, Sum.elim v w ∈ s} := by
  have h := hs.image_comp (Sum.inl : α → α ⊕ β)
  convert h using 1
  ext v
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨Sum.elim v w, hw, rfl⟩
  · rintro ⟨x, hx, hxi⟩
    refine ⟨x ∘ Sum.inr, ?_⟩
    have he : Sum.elim v (x ∘ Sum.inr) = x := by
      funext a
      cases a with
      | inl a => exact (congrFun hxi a).symm
      | inr b => rfl
    rwa [he]

theorem realDefinable_forall {α β : Type*} [Finite α] [Finite β]
    {s : Set ((α ⊕ β) → ℝ)}
    (hs : (Set.univ : Set ℝ).Definable Language.ring s) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | ∀ w : β → ℝ, Sum.elim v w ∈ s} := by
  simpa only [Set.compl_setOf, Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_not]
    using (realDefinable_exists hs.compl).compl

theorem realDefinable_finite_all {α ι : Type*} [Fintype ι]
    {s : ι → Set (α → ℝ)}
    (hs : ∀ i, (Set.univ : Set ℝ).Definable Language.ring (s i)) :
    (Set.univ : Set ℝ).Definable Language.ring {v | ∀ i, v ∈ s i} := by
  simpa [Set.setOf_forall] using Set.definable_finset_biInter hs Finset.univ

theorem realPolynomial_nonneg_definable {α : Type*} [Finite α]
    (p : MvPolynomial α ℝ) :
    (Set.univ : Set ℝ).Definable Language.ring {v : α → ℝ | 0 ≤ MvPolynomial.eval v p} := by
  let q : MvPolynomial (α ⊕ Unit) ℝ :=
    MvPolynomial.rename Sum.inl p - MvPolynomial.X (Sum.inr ()) ^ 2
  have h := realDefinable_exists (realPolynomial_zero_definable q)
  convert h using 1
  ext v
  simp only [Set.mem_setOf_eq, q, map_sub, map_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, Function.comp_def, Sum.elim_inl, Sum.elim_inr, sub_eq_zero]
  constructor
  · intro hp
    exact ⟨fun _ => Real.sqrt (MvPolynomial.eval v p), (Real.sq_sqrt hp).symm⟩
  · rintro ⟨w, hw⟩
    rw [hw]
    exact sq_nonneg _

theorem realPolynomial_le_definable {α : Type*} [Finite α]
    (p q : MvPolynomial α ℝ) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | MvPolynomial.eval v p ≤ MvPolynomial.eval v q} := by
  simpa only [map_sub, sub_nonneg] using realPolynomial_nonneg_definable (q - p)

end PaperI
