import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Data.Set.Card

/-! Finite multiplicity controls the sum of image measures of disjoint
injective pieces. The actual fiber must be finite: Nat.card alone would assign
zero to an infinite fiber. No global injectivity is assumed. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace PaperI
attribute [local instance] Classical.propDecidable

/-- Distinct disjoint pieces meeting an output yield distinct selected preimages. -/
theorem image_piece_count_le_fiber_card
    {α β : Type*} (f : α → β) (s : Set α) (t : ℕ → Set α)
    (hsub : ∀ i, t i ⊆ s) (hdisj : Pairwise (fun i j => Disjoint (t i) (t j)))
    (y : β) (hfin : Finite {x : α | x ∈ s ∧ f x = y}) (F : Finset ℕ) :
    (F.filter (fun i => y ∈ f '' t i)).card ≤ Nat.card {x : α | x ∈ s ∧ f x = y} := by
  classical
  letI := hfin
  let I := F.filter (fun i => y ∈ f '' t i)
  have hex (i : I) : ∃ x, x ∈ t i ∧ f x = y := (Finset.mem_filter.mp i.property).2
  let g : I → {x : α | x ∈ s ∧ f x = y} := fun i =>
    ⟨(hex i).choose, hsub i (hex i).choose_spec.1, (hex i).choose_spec.2⟩
  have hinj : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hx : (hex i).choose = (hex j).choose := congrArg Subtype.val hij
    exact Set.disjoint_left.mp (hdisj hne) (hex i).choose_spec.1
      (hx.symm ▸ (hex j).choose_spec.1)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using Nat.card_le_card_of_injective g hinj

/-- For countably many disjoint selected pieces, multiplicity at most N bounds
the sum of their image measures by N times the target measure. -/
theorem tsum_image_measure_le_of_fiber_bound
    {α β : Type*} [MeasurableSpace β] (μ : Measure β)
    (f : α → β) (s : Set α) (t : ℕ → Set α) (Q : Set β) (hQ : MeasurableSet Q)
    (hsub : ∀ i, t i ⊆ s) (hdisj : Pairwise (fun i j => Disjoint (t i) (t j)))
    (himage : ∀ i, MeasurableSet (f '' t i)) (hto : ∀ i, f '' t i ⊆ Q)
    (N : ℕ) (hN : ∀ y, Finite {x : α | x ∈ s ∧ f x = y} ∧
      Nat.card {x : α | x ∈ s ∧ f x = y} ≤ N) :
    (∑' i, μ (f '' t i)) ≤ (N : ℝ≥0∞) * μ Q := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  calc
    ∑ i ∈ F, μ (f '' t i) =
        ∫⁻ y, ∑ i ∈ F, (f '' t i).indicator (fun _ => (1 : ℝ≥0∞)) y ∂μ := by
      rw [lintegral_finset_sum F (fun i _ => measurable_const.indicator (himage i))]
      simp only [lintegral_indicator (himage _), setLIntegral_one]
    _ ≤ ∫⁻ y, Q.indicator (fun _ => (N : ℝ≥0∞)) y ∂μ := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ Q
      · rw [Set.indicator_of_mem hy]
        have hc := (image_piece_count_le_fiber_card f s t hsub hdisj y (hN y).1 F).trans
          (hN y).2
        have he : (∑ i ∈ F, (f '' t i).indicator (fun _ => (1 : ℝ≥0∞)) y) =
            ((F.filter (fun i => y ∈ f '' t i)).card : ℝ≥0∞) := by
          simp [Set.indicator, Finset.sum_boole]
        rw [he]
        exact_mod_cast hc
      · rw [Set.indicator_of_not_mem hy]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro i hi
        exact Set.indicator_of_not_mem (fun h => hy (hto i h)) _
    _ = (N : ℝ≥0∞) * μ Q := by rw [lintegral_indicator hQ, setLIntegral_const]

end PaperI
