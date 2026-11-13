import PaperILean.PublishedQuantitativeQE
import PaperILean.BoundedPolynomialTuple
import PaperILean.PolynomialSignPullbackDegree
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Original-route projection/QE bridge. Bounds precede all coefficients and
sets. The only published input is the existing quantitative QE contract.
Pre-strategy checks: evidence/original_route_124_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem polynomialPrenexSet_one_exists {α : Type*} {s : ℕ}
    (p : Fin s → MvPolynomial (α ⊕ Fin 1) ℝ)
    (b : (Fin s → Bool × Bool) → Bool) :
    polynomialPrenexSet [(false, 1)] p b =
      {x : α → ℝ | ∃ t : ℝ, Sum.elim x (fun _ => t) ∈ polynomialBooleanSet p b} := by
  ext x
  change (∃ y : Fin 1 → ℝ, Sum.elim x (Fin.append y Fin.elim0) ∈
    polynomialBooleanSet p b) ↔ _
  have he (y : Fin 1 → ℝ) : Fin.append y Fin.elim0 = fun _ => y 0 := by
    funext i
    fin_cases i
    rfl
  simp only [he]
  exact ⟨fun ⟨y, hy⟩ => ⟨y 0, hy⟩, fun ⟨t, ht⟩ => ⟨fun _ => t, ht⟩⟩

theorem published_bounded_time_projection_format
    (hQQE : PublishedQuantitativeRealQE) (α : Type) [Fintype α] (s D : ℕ) :
    ∃ sOut DOut : ℕ,
    ∀ (A : Finset (MvPolynomial (α ⊕ Fin 1) ℝ))
      (S : Set ((α ⊕ Fin 1) → ℝ)),
    A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A S →
    ∃ B : Finset (MvPolynomial α ℝ), B.card ≤ sOut ∧
      (∀ p ∈ B, p.totalDegree ≤ DOut) ∧
      PolynomialSignDetermined B {x : α → ℝ | ∃ t : ℝ, Sum.elim x (fun _ => t) ∈ S} := by
  obtain ⟨sOut, DOut, h⟩ := published_quantified_polynomial_sign_format hQQE α [(false,1)] s D
  refine ⟨sOut, DOut, ?_⟩
  intro A S hc hd hS
  obtain ⟨p, hp, hSp⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hc hd hS
  obtain ⟨b, rfl⟩ := polynomialSignDetermined_exists_boolean_table p S hSp
  simpa only [polynomialPrenexSet_one_exists] using h p hp b

theorem bounded_sign_format_closed_coordinate_restriction {α : Type*}
    (A : Finset (MvPolynomial α ℝ)) (S : Set (α → ℝ)) (s D : ℕ)
    (hc : A.card ≤ s) (hd : ∀ p ∈ A, p.totalDegree ≤ D)
    (hS : PolynomialSignDetermined A S) (j : α) (a b : ℝ) :
    ∃ B : Finset (MvPolynomial α ℝ), B.card ≤ s+2 ∧
      (∀ p ∈ B, p.totalDegree ≤ max D 1) ∧
      PolynomialSignDetermined B {x | x ∈ S ∧ x j ∈ Icc a b} := by
  let L : MvPolynomial α ℝ := (MvPolynomial.X j : MvPolynomial α ℝ) -
    (MvPolynomial.C a : MvPolynomial α ℝ)
  let R : MvPolynomial α ℝ := (MvPolynomial.C b : MvPolynomial α ℝ) -
    (MvPolynomial.X j : MvPolynomial α ℝ)
  have hL : L.totalDegree ≤ 1 := (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  have hR : R.totalDegree ≤ 1 := (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  refine ⟨(A ∪ {L}) ∪ {R}, ?_, ?_, ?_⟩
  · calc
      _ ≤ (A ∪ {L}).card + 1 := by simpa using Finset.card_union_le (A ∪ {L}) {R}
      _ ≤ A.card + 1 + 1 := Nat.add_le_add_right (by simpa using Finset.card_union_le A {L}) 1
      _ ≤ s+2 := by omega
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact (hd p hp).trans (Nat.le_max_left _ _)
      · rw [Finset.mem_singleton.mp hp]
        exact hL.trans (Nat.le_max_right _ _)
    · rw [Finset.mem_singleton.mp hp]
      exact hR.trans (Nat.le_max_right _ _)
  · intro x y hxy
    have hs := hS x y (fun p hp => hxy p (Finset.mem_union_left _ (Finset.mem_union_left _ hp)))
    have hl := realSignEquivalent_nonneg (hxy L
      (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))))
    have hr := realSignEquivalent_nonneg (hxy R (Finset.mem_union_right _ (Finset.mem_singleton_self _)))
    simp only [L, R, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_nonneg] at hl hr
    exact and_congr hs (and_congr hl hr)

end PaperI
