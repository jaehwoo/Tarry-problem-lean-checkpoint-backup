import PaperILean.RegularCoefficientFiberTopology
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-! I665: measurable countable injective partition of a regular square map.
This is a checked localization of the area argument: only pointwise ambient
derivatives with nonzero determinant are required. No global Lipschitz bound
is inferred from polynomiality. Pre-strategy: checkpoint_107_area_prestrategy. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace PaperI

/-- A regular square map admits a countable disjoint measurable partition
of any measurable selected domain, with injectivity on each piece. -/
theorem exists_measurable_injective_partition_of_det_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → E) (s : Set E) (hs : MeasurableSet s)
    (f' : E → E →L[ℝ] E)
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hdet : ∀ x ∈ s, (f' x).det ≠ 0) :
    ∃ t : ℕ → Set E, (∀ n, MeasurableSet (t n)) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      (⋃ n, t n) = s ∧ (∀ n, InjOn f (t n)) := by
  classical
  by_cases hE : Subsingleton E
  · exact ⟨fun n => if n = 0 then s else ∅,
      fun n => by dsimp; split_ifs <;> simp_all,
      by intro i j hij; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp_all,
      by ext x; simp,
      fun _ _ _ _ _ _ => hE.elim _ _⟩
  haveI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
  let r : (E →L[ℝ] E) → ℝ≥0 := fun A =>
    if h : A.det ≠ 0 then
      ‖((A.toContinuousLinearEquivOfDetNeZero h).symm : E →L[ℝ] E)‖₊⁻¹ / 2
    else 1
  have hr : ∀ A, r A ≠ 0 := by
    intro A
    by_cases h : A.det ≠ 0
    · rw [show r A = _ from dif_pos h]
      exact ne_of_gt (div_pos (inv_pos.mpr (by
        exact_mod_cast (A.toContinuousLinearEquivOfDetNeZero h).symm.norm_pos)) (by norm_num))
    · simp [r, h]
  obtain ⟨u, A, hdisj, hmeas, hcover, happ, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f'
      (fun x hx => (hf' x hx).hasFDerivWithinAt) r hr
  refine ⟨fun n => s ∩ u n, fun n => hs.inter (hmeas n),
    fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right, ?_, ?_⟩
  · rw [← inter_iUnion]
    exact inter_eq_left.mpr hcover
  · intro n
    by_cases hnon : s.Nonempty
    · obtain ⟨y, hy, hAy⟩ := hA hnon n
      have hn : (A n).det ≠ 0 := hAy ▸ hdet y hy
      let L := (A n).toContinuousLinearEquivOfDetNeZero hn
      have happ' : ApproximatesLinearOn f (L : E →L[ℝ] E) (s ∩ u n)
          (‖(L.symm : E →L[ℝ] E)‖₊⁻¹ / 2) := by
        simpa [L, r, hn] using happ n
      apply happ'.injOn (Or.inr _)
      exact half_lt_self (inv_pos.mpr (by exact_mod_cast L.symm.norm_pos))
    · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hnon
      simp [he]

end PaperI
