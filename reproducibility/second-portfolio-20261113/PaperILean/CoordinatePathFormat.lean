import PaperILean.ScalarRelationComposition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded

/-! Concrete coordinate-function inputs for the I1263 path application.
The partial graph retains S, its format is computed from S rather than assumed,
and the range estimate uses the Euclidean diameter through an explicit L2
coordinate identification. The default supremum norm on functions is not
identified with the Euclidean norm. Pre-strategy: checkpoint108 record009. -/

noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def coordinateGraphPolynomial {κ : Type*} (i : κ) : MvPolynomial (κ ⊕ Unit) ℝ :=
  MvPolynomial.X (Sum.inr ()) - MvPolynomial.X (Sum.inl i)

theorem coordinateGraphPolynomial_totalDegree_le {κ : Type*} (i : κ) :
    (coordinateGraphPolynomial i).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  simp

theorem coordinate_graph_sign_description {κ : Type*}
    (A : Finset (MvPolynomial κ ℝ)) (S : Set (κ → ℝ))
    (hS : PolynomialSignDetermined A S) (i : κ) :
    PolynomialSignDetermined
      (A.image (MvPolynomial.rename Sum.inl) ∪ {coordinateGraphPolynomial i})
      (scalarFunctionGraph S (fun x => x i)) := by
  intro x y hxy
  have hDom : (fun k => x (Sum.inl k)) ∈ S ↔ (fun k => y (Sum.inl k)) ∈ S := by
    apply hS
    intro q hq
    simpa only [MvPolynomial.eval_rename, Function.comp_def] using
      hxy (MvPolynomial.rename Sum.inl q)
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
  have hEq := (hxy (coordinateGraphPolynomial i)
    (Finset.mem_union_right _ (Finset.mem_singleton_self _))).1
  simp only [coordinateGraphPolynomial, map_sub, MvPolynomial.eval_X, sub_eq_zero] at hEq
  exact and_congr hDom hEq

/-- An exact partial coordinate graph needs at most one more polynomial than
S, and degree at most max D 1. Zero/repeated atoms need no special exclusions. -/
theorem coordinate_graph_bounded_sign_format {κ : Type*}
    (A : Finset (MvPolynomial κ ℝ)) (S : Set (κ → ℝ)) (s D : ℕ)
    (hcard : A.card ≤ s) (hdeg : ∀ q ∈ A, q.totalDegree ≤ D)
    (hS : PolynomialSignDetermined A S) (i : κ) :
    ∃ B : Finset (MvPolynomial (κ ⊕ Unit) ℝ), B.card ≤ s + 1 ∧
      (∀ q ∈ B, q.totalDegree ≤ max D 1) ∧
      PolynomialSignDetermined B (scalarFunctionGraph S (fun x => x i)) := by
  classical
  refine ⟨A.image (MvPolynomial.rename Sum.inl) ∪ {coordinateGraphPolynomial i}, ?_, ?_,
    coordinate_graph_sign_description A S hS i⟩
  · calc
      _ ≤ (A.image (MvPolynomial.rename Sum.inl)).card +
          ({coordinateGraphPolynomial i} : Finset _).card := Finset.card_union_le _ _
      _ ≤ s + 1 := by
        simpa only [Finset.card_singleton] using
          Nat.add_le_add_right ((Finset.card_image_le).trans hcard) 1
  · intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      exact (MvPolynomial.totalDegree_rename_le _ _).trans ((hdeg p hp).trans (Nat.le_max_left _ _))
    · rw [Finset.mem_singleton.mp hq]
      exact (coordinateGraphPolynomial_totalDegree_le i).trans (Nat.le_max_right _ _)

/-- The manuscript diameter is Euclidean. It is not replaced by the default
supremum-norm diameter on the coordinate-function type. -/
theorem coordinate_range_le_euclidean_diameter {κ : Type*} [Fintype κ]
    (S : Set (κ → ℝ))
    (hS : Bornology.IsBounded ((WithLp.equiv 2 (κ → ℝ)).symm '' S)) (i : κ)
    (x : κ → ℝ) (hx : x ∈ S) (y : κ → ℝ) (hy : y ∈ S) :
    |x i - y i| ≤ Metric.diam ((WithLp.equiv 2 (κ → ℝ)).symm '' S) := by
  have hcoord := PiLp.dist_apply_le ((WithLp.equiv 2 (κ → ℝ)).symm x)
    ((WithLp.equiv 2 (κ → ℝ)).symm y) i
  have hdiam := Metric.dist_le_diam_of_mem hS (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
  calc
    |x i - y i| ≤ dist ((WithLp.equiv 2 (κ → ℝ)).symm x)
        ((WithLp.equiv 2 (κ → ℝ)).symm y) := by
      simpa only [WithLp.equiv_symm_pi_apply, Real.dist_eq] using hcoord
    _ ≤ Metric.diam ((WithLp.equiv 2 (κ → ℝ)).symm '' S) := hdiam

end PaperI
