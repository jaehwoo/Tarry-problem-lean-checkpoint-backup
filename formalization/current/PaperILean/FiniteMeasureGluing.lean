import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Disjointed

/-! Finite measurable patch gluing. Compatibility is an explicit proved input;
no local measure is silently identified with a global one. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PaperI

def finiteChartGluedMeasure {α : Type*} [MeasurableSpace α] {n : ℕ}
    (U : Fin n → Set α) (μ : Fin n → Measure α) : Measure α :=
  Measure.sum (fun i => (μ i).restrict (disjointed U i))

theorem finiteChartPart_measurable {α : Type*} [MeasurableSpace α] {n : ℕ}
    (U : Fin n → Set α) (hU : ∀ i, MeasurableSet (U i)) (i : Fin n) :
    MeasurableSet (disjointed U i) :=
  disjointedRec (fun _ j ht => ht.diff (hU j)) (hU i)

theorem finiteChartGluedMeasure_agrees {α : Type*} [MeasurableSpace α] {n : ℕ}
    (U : Fin n → Set α) (μ : Fin n → Measure α)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    (ν : Measure α) (A : Set α) (hA : MeasurableSet A)
    (hcompat : ∀ i B, MeasurableSet B → B ⊆ A ∩ U i → μ i B = ν B) :
    (finiteChartGluedMeasure U μ).restrict A = ν.restrict A := by
  have hparts : ⋃ i, disjointed U i = univ := by rw [iUnion_disjointed, hcover]
  have hsum : Measure.sum (fun i => ν.restrict (disjointed U i)) = ν := by
    rw [← Measure.restrict_iUnion (disjoint_disjointed U) (finiteChartPart_measurable U hU),
      hparts, Measure.restrict_univ]
  calc
    (finiteChartGluedMeasure U μ).restrict A =
        Measure.sum (fun i => ((μ i).restrict (disjointed U i)).restrict A) :=
      Measure.restrict_sum_of_countable _ _
    _ = Measure.sum (fun i => (ν.restrict (disjointed U i)).restrict A) := by
      congr 1
      funext i
      apply Measure.ext
      intro B hB
      rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
        Measure.restrict_apply (hB.inter hA), Measure.restrict_apply (hB.inter hA)]
      apply hcompat i _ ((hB.inter hA).inter (finiteChartPart_measurable U hU i))
      intro x hx
      exact ⟨hx.1.2, disjointed_subset U i hx.2⟩
    _ = (Measure.sum (fun i => ν.restrict (disjointed U i))).restrict A :=
      (Measure.restrict_sum_of_countable _ _).symm
    _ = ν.restrict A := by rw [hsum]

theorem finiteChartGluedMeasure_finite {α : Type*} [MeasurableSpace α] {n : ℕ}
    (U : Fin n → Set α) (μ : Fin n → Measure α)
    (hfin : ∀ i, μ i (U i) < ⊤) :
    (finiteChartGluedMeasure U μ) univ < ⊤ := by
  rw [finiteChartGluedMeasure, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro i _
  rw [Measure.restrict_apply_univ]
  exact (measure_mono (disjointed_subset U i)).trans_lt (hfin i)

end PaperI
