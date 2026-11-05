import PaperILean.PolynomialSignDescription

/-! A finite polynomial sign description is locally constant away from
the zero sets of its nonzero polynomials. Identically zero atoms are retained
as tautological sign data, not used as spurious nonzero annihilators. -/

noncomputable section
open Filter
open scoped Topology
namespace PaperI

theorem continuousAt_eventually_realSignEquivalent {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {x : X} (hf : ContinuousAt f x) (hx : f x ≠ 0) :
    ∀ᶠ y in 𝓝 x, RealSignEquivalent (f x) (f y) := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · filter_upwards [hf.eventually_lt_const hn] with y hy
    exact ⟨iff_of_false (ne_of_lt hn) (ne_of_lt hy),
      iff_of_false (not_lt_of_ge hn.le) (not_lt_of_ge hy.le)⟩
  · filter_upwards [hf.eventually_const_lt hp] with y hy
    exact ⟨iff_of_false (ne_of_gt hp) (ne_of_gt hy), iff_of_true hp hy⟩

theorem polynomial_signs_eventually_constant {X α : Type*} [TopologicalSpace X]
    (A : Finset (MvPolynomial α ℝ)) {v : X → (α → ℝ)} {x : X}
    (hv : ContinuousAt v x)
    (hnz : ∀ p ∈ A, p ≠ 0 → MvPolynomial.eval (v x) p ≠ 0) :
    ∀ᶠ y in 𝓝 x, ∀ p ∈ A,
      RealSignEquivalent (MvPolynomial.eval (v x) p) (MvPolynomial.eval (v y) p) := by
  apply (Filter.eventually_all_finset A).mpr
  intro p hp
  by_cases hz : p = 0
  · subst p
    exact Filter.Eventually.of_forall (fun _ => by simpa using realSignEquivalent_refl 0)
  · exact continuousAt_eventually_realSignEquivalent
      (p.continuous_eval.continuousAt.comp hv) (hnz p hp hz)

theorem polynomialSignDetermined_eventually_membership {X α : Type*}
    [TopologicalSpace X] {A : Finset (MvPolynomial α ℝ)} {S : Set (α → ℝ)}
    (hS : PolynomialSignDetermined A S) {v : X → (α → ℝ)} {x : X}
    (hv : ContinuousAt v x)
    (hnz : ∀ p ∈ A, p ≠ 0 → MvPolynomial.eval (v x) p ≠ 0) :
    ∀ᶠ y in 𝓝 x, v x ∈ S ↔ v y ∈ S := by
  filter_upwards [polynomial_signs_eventually_constant A hv hnz] with y hy
  exact hS (v x) (v y) hy

end PaperI
