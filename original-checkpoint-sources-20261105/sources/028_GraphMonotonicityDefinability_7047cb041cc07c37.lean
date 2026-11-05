import PaperILean.MonotonicityBadSet
import PaperILean.RealPolynomialDefinability

/-! The exceptional monotonicity locus is definable from the actual function
graph. Comparisons use one value at each input. The later representation lemma
needs graph correctness only on the original closed interval, and no extension
of the graph outside that interval. No monotonicity theorem is assumed here. -/

noncomputable section
open FirstOrder Set
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

abbrev MonotonicityBase (α : Type*) := (α ⊕ Fin 2) ⊕ Unit
abbrev MonotonicityWindow (α : Type*) := MonotonicityBase α ⊕ Fin 2

/-- All comparisons in an open window, with two graph values quantified
together. Coordinates of `q` are input, input, value, value. -/
def graphIntervalCondition {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ))
    (S : Set (Fin 4 → ℝ)) : Set (MonotonicityWindow α → ℝ) :=
  {v | ∀ q : Fin 4 → ℝ,
    q 0 ∈ Ioo (v (Sum.inr 0)) (v (Sum.inr 1)) →
    q 1 ∈ Ioo (v (Sum.inr 0)) (v (Sum.inr 1)) →
    Sum.elim (fun a => v (Sum.inl (Sum.inl (Sum.inl a)))) ![q 0, q 2] ∈ G →
    Sum.elim (fun a => v (Sum.inl (Sum.inl (Sum.inl a)))) ![q 1, q 3] ∈ G → q ∈ S}

theorem realCoordinate_lt_definable {α : Type*} [Finite α] (i j : α) :
    (univ : Set ℝ).Definable Language.ring {v : α → ℝ | v i < v j} := by
  simpa only [MvPolynomial.eval_X, Set.compl_setOf, not_le] using
    (realPolynomial_le_definable (MvPolynomial.X j) (MvPolynomial.X i)).compl

theorem realCoordinate_eq_definable {α : Type*} [Finite α] (i j : α) :
    (univ : Set ℝ).Definable Language.ring {v : α → ℝ | v i = v j} := by
  have h := (realPolynomial_le_definable (MvPolynomial.X i) (MvPolynomial.X j)).inter
    (realPolynomial_le_definable (MvPolynomial.X j) (MvPolynomial.X i))
  simpa only [Set.inter_setOf_eq, MvPolynomial.eval_X, le_antisymm_iff] using h

theorem graphIntervalCondition_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)} {S : Set (Fin 4 → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G)
    (hS : (univ : Set ℝ).Definable Language.ring S) :
    (univ : Set ℝ).Definable Language.ring (graphIntervalCondition G S) := by
  let e₀ : α ⊕ Fin 2 → MonotonicityWindow α ⊕ Fin 4 :=
    Sum.elim (fun a => Sum.inl (Sum.inl (Sum.inl (Sum.inl a))))
      (fun i => Sum.inr (if i = 0 then 0 else 2))
  let e₁ : α ⊕ Fin 2 → MonotonicityWindow α ⊕ Fin 4 :=
    Sum.elim (fun a => Sum.inl (Sum.inl (Sum.inl (Sum.inl a))))
      (fun i => Sum.inr (if i = 0 then 1 else 3))
  have h₀ := (realCoordinate_lt_definable (Sum.inl (Sum.inr 0) : MonotonicityWindow α ⊕ Fin 4) (Sum.inr 0)).inter
    (realCoordinate_lt_definable (Sum.inr 0) (Sum.inl (Sum.inr 1)))
  have h₁ := (realCoordinate_lt_definable (Sum.inl (Sum.inr 0) : MonotonicityWindow α ⊕ Fin 4) (Sum.inr 1)).inter
    (realCoordinate_lt_definable (Sum.inr 1) (Sum.inl (Sum.inr 1)))
  have h := realDefinable_forall
    ((h₀.inter (h₁.inter ((hG.preimage_comp e₀).inter (hG.preimage_comp e₁)))).compl.union
      (hS.preimage_comp Sum.inr))
  convert h using 1
  ext v
  simp only [graphIntervalCondition, mem_setOf_eq, mem_union, mem_compl_iff,
    mem_inter_iff, mem_preimage, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  apply forall_congr'
  intro q
  have he₀ : (fun a => Sum.elim v q (e₀ a)) =
      Sum.elim (fun a => v (Sum.inl (Sum.inl (Sum.inl a)))) ![q 0, q 2] := by
    funext a
    rcases a with a | i
    · rfl
    · fin_cases i <;> rfl
  have he₁ : (fun a => Sum.elim v q (e₁ a)) =
      Sum.elim (fun a => v (Sum.inl (Sum.inl (Sum.inl a)))) ![q 1, q 3] := by
    funext a
    rcases a with a | i
    · rfl
    · fin_cases i <;> rfl
  rw [he₀, he₁]
  simp only [mem_Ioo]
  tauto

def increasingGraphComparisons : Set (Fin 4 → ℝ) := {q | q 0 < q 1 → q 2 < q 3}
def decreasingGraphComparisons : Set (Fin 4 → ℝ) := {q | q 0 < q 1 → q 3 < q 2}
def constantGraphComparisons : Set (Fin 4 → ℝ) := {q | q 2 = q 3}

def graphMonotonicityGoodRelation {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ)) :
    Set (MonotonicityBase α → ℝ) :=
  {v | ∃ w : Fin 2 → ℝ,
    v (Sum.inl (Sum.inr 0)) ≤ w 0 ∧ w 1 ≤ v (Sum.inl (Sum.inr 1)) ∧
    w 0 < v (Sum.inr ()) ∧ v (Sum.inr ()) < w 1 ∧
      (Sum.elim v w ∈ graphIntervalCondition G increasingGraphComparisons ∨
       Sum.elim v w ∈ graphIntervalCondition G decreasingGraphComparisons ∨
       Sum.elim v w ∈ graphIntervalCondition G constantGraphComparisons)}

def graphMonotonicityBadRelation {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ)) :
    Set (MonotonicityBase α → ℝ) :=
  {v | v (Sum.inr ()) ∈ Ioo (v (Sum.inl (Sum.inr 0))) (v (Sum.inl (Sum.inr 1))) ∧
    v ∉ graphMonotonicityGoodRelation G}

theorem graphMonotonicityGoodRelation_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (graphMonotonicityGoodRelation G) := by
  have hi : (univ : Set ℝ).Definable Language.ring increasingGraphComparisons := by
    convert (realCoordinate_lt_definable (0 : Fin 4) 1).compl.union
      (realCoordinate_lt_definable (2 : Fin 4) 3) using 1
    ext q; simp [increasingGraphComparisons, or_iff_not_imp_left]
  have hd : (univ : Set ℝ).Definable Language.ring decreasingGraphComparisons := by
    convert (realCoordinate_lt_definable (0 : Fin 4) 1).compl.union
      (realCoordinate_lt_definable (3 : Fin 4) 2) using 1
    ext q; simp [decreasingGraphComparisons, or_iff_not_imp_left]
  have hc : (univ : Set ℝ).Definable Language.ring constantGraphComparisons :=
    realCoordinate_eq_definable 2 3
  have hl := realPolynomial_le_definable
    (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr 0)) : MonotonicityWindow α))
    (MvPolynomial.X (Sum.inr 0))
  have hr := realPolynomial_le_definable
    (MvPolynomial.X (Sum.inr 1 : MonotonicityWindow α))
    (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr 1))))
  have hx := realCoordinate_lt_definable (Sum.inr 0 : MonotonicityWindow α)
    (Sum.inl (Sum.inr ()))
  have hy := realCoordinate_lt_definable (Sum.inl (Sum.inr ()) : MonotonicityWindow α)
    (Sum.inr 1)
  exact realDefinable_exists (by
    simpa only [mem_inter_iff, mem_union, mem_setOf_eq, MvPolynomial.eval_X] using
      hl.inter (hr.inter (hx.inter (hy.inter
        ((graphIntervalCondition_definable hG hi).union
          ((graphIntervalCondition_definable hG hd).union (graphIntervalCondition_definable hG hc)))))))

theorem graphMonotonicityBadRelation_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (graphMonotonicityBadRelation G) := by
  exact ((realCoordinate_lt_definable (Sum.inl (Sum.inr 0)) (Sum.inr ())).inter
    (realCoordinate_lt_definable (Sum.inr ()) (Sum.inl (Sum.inr 1)))).inter
      (graphMonotonicityGoodRelation_definable hG).compl

end PaperI
