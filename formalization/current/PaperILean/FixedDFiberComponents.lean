import PaperILean.PublishedFormatComponents
import Mathlib.Algebra.MvPolynomial.CommRing

/-! I3237[366,443): the actual original-coordinate d-fiber component count.
The ambient sign description is given; the fiber description is proved by
inserting the literal equation X 3 - C t. The bound is chosen before all
polynomial coefficients and all real fiber levels. Both component finiteness
and the natural cardinality bound are retained. -/
noncomputable section
namespace PaperI.FixedDFiberComponents

/-- The actual d=t fiber of an ambient sign-described set has format
(s+1,max D 1), including constant ambient atoms and repeated slice atoms. -/
theorem actual_d_fiber_sign_format
    (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ))
    (s D : ℕ) (hAc : A.card ≤ s) (hAd : ∀ p ∈ A, p.totalDegree ≤ D)
    (hAE : PolynomialSignDetermined A E) (t : ℝ) :
    ∃ B : Finset (MvPolynomial (Fin 6) ℝ), B.card ≤ s+1 ∧
      (∀ p ∈ B, p.totalDegree ≤ max D 1) ∧
      PolynomialSignDetermined B {g | g ∈ E ∧ g 3 = t} := by
  classical
  let q : MvPolynomial (Fin 6) ℝ := MvPolynomial.X 3 - MvPolynomial.C t
  refine ⟨insert q A, (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hAc 1), ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · have hq : q.totalDegree ≤ 1 := by
        simpa only [q, MvPolynomial.totalDegree_X] using
          (MvPolynomial.totalDegree_sub_C_le (MvPolynomial.X (3 : Fin 6)) t)
      exact hq.trans (Nat.le_max_right D 1)
    · exact (hAd p hp).trans (Nat.le_max_left D 1)
  · intro x y hxy
    have hambient : x ∈ E ↔ y ∈ E :=
      hAE x y (fun p hp => hxy p (Finset.mem_insert_of_mem hp))
    have hlevel : x 3 = t ↔ y 3 = t := by
      simpa only [q, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero]
        using (hxy q (Finset.mem_insert_self q A)).1
    exact and_congr hambient hlevel

/-- Complete actual fixed-d fiber count. N is uniform before every ambient
polynomial coefficient, sign-selected set E, and real level t. No fiber-format,
nonempty-fiber, compactness, finite-component or path hypothesis is supplied. -/
theorem actual_d_fiber_component_count_stage
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ N : ℕ, ∀ (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A E →
      ∀ t : ℝ, Finite (ConnectedComponents {g : Fin 6 → ℝ | g ∈ E ∧ g 3 = t}) ∧
        Nat.card (ConnectedComponents {g : Fin 6 → ℝ | g ∈ E ∧ g 3 = t}) ≤ N := by
  obtain ⟨N,hN⟩ := published_bounded_sign_format_component_bound
    hCell hHardt hQE (Fin 6) (s+1) (max D 1)
  refine ⟨N,?_⟩
  intro A E hAc hAd hAE t
  obtain ⟨B,hBc,hBd,hBE⟩ := actual_d_fiber_sign_format A E s D hAc hAd hAE t
  exact hN B {g : Fin 6 → ℝ | g ∈ E ∧ g 3 = t} hBc hBd hBE

end PaperI.FixedDFiberComponents
