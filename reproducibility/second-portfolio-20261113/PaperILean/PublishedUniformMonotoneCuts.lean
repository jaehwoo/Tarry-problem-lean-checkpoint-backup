import PaperILean.PublishedScalarMonotonicity
import PaperILean.PublishedScalarFiniteFibers
import PaperILean.FiniteMonotonicityCuts
import PaperILean.GraphMonotonicityRealization
import PaperILean.GraphScalarSlice

/-! Uniform individual monotonicity cuts for one fixed definable graph family.
Qualitative published monotonicity proves the actual exceptional fibers finite;
the independently checked Hardt/component application supplies their common
cardinality bound. No external contract assumes a uniform monotonicity count.
All real parameters and both endpoints follow the bound. Continuity on the
closed interval remains explicit. No path construction or analytic assertion
is made by this module, and this fixed-family bound is not yet a format-only
universal family theorem. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem scalar_bad_fiber_eq_monotonicityBadSet {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) :
    scalarProjectionFiber (graphMonotonicityBadRelation G) (Sum.elim p ![a,b]) =
      MonotonicityBadSet f a b := by
  ext x
  exact graphMonotonicityBadRelation_realize_iff G p f a b x hG

/-- The bound is fixed before every graph parameter, represented function, and
interval. Graph correctness is needed only on that interval. -/
theorem published_uniform_monotone_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ K : ℕ, ∀ (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ),
      a ≤ b → ContinuousOn f (Icc a b) →
      (∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        MonotoneOnCutIntervals f C ∧ C.card ≤ K := by
  have hBad := hQE.finite_sign_description _ (graphMonotonicityBadRelation_definable hG)
  obtain ⟨N, hN⟩ := published_scalar_finite_fiber_card_bound
    hCell hHardt hQE (graphMonotonicityBadRelation G) hBad
  refine ⟨N + 2, ?_⟩
  intro p f a b hab hf hrep
  have hGraph := published_openScalarGraph_sign_description hQE hG p f a b hrep
  have hfin := published_monotonicityBadSet_finite hMono f a b hGraph
  have he := scalar_bad_fiber_eq_monotonicityBadSet G p f a b hrep
  have hcard : Nat.card (MonotonicityBadSet f a b) ≤ N := by
    have h := hN (Sum.elim p ![a,b]) (he.symm ▸ hfin)
    simpa only [he] using h
  obtain ⟨C, ha, hb, hC, hm, hc⟩ := exists_monotone_cut_set_of_finite_bad_set hab hf hfin
  exact ⟨C, ha, hb, hC, hm, hc.trans (Nat.add_le_add_right hcard 2)⟩

/-- A simultaneous partition for finitely many represented functions, allowing
different parameters for each function. The common bound precedes all of them. -/
theorem published_uniform_common_monotone_partition
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity)
    {α ι : Type} [Finite α] [Fintype ι] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ M : ℕ, ∀ (p : ι → α → ℝ) (f : ι → ℝ → ℝ) (a b : ℝ),
      a ≤ b → (∀ i, ContinuousOn (f i) (Icc a b)) →
      (∀ i, ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim (p i) ![t,y] ∈ G ↔ y = f i t) →
      ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ M ∧ t 0 = a ∧ t n = b ∧
        MonotoneOn t (Icc 0 n) ∧
        ∀ j < n, ∀ i, MonotoneOn (f i) (Ioo (t j) (t (j + 1))) ∨
          AntitoneOn (f i) (Ioo (t j) (t (j + 1))) := by
  obtain ⟨K, hK⟩ := published_uniform_monotone_cut_sets hCell hHardt hQE hMono G hG
  refine ⟨1 + ∑ _ : ι, K, ?_⟩
  intro p f a b hab hf hrep
  exact exists_common_partition_of_individual_subdivisions f (fun _ => K) hab
    (fun i => hK (p i) (f i) a b hab (hf i) (hrep i))

/-- The variation constant is independent of every real graph parameter and
range bound. Its dependence on the fixed family and number of functions remains. -/
theorem published_uniform_graph_family_variation
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity)
    {α ι : Type} [Finite α] [Fintype ι] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ M : ℕ, ∀ (p : ι → α → ℝ) (f : ι → ℝ → ℝ) (a b : ℝ) (B : ι → ℝ),
      a ≤ b → (∀ i, ContinuousOn (f i) (Icc a b)) →
      (∀ i, ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim (p i) ![t,y] ∈ G ↔ y = f i t) →
      (∀ i, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f i x - f i y| ≤ B i) →
      ∀ i, BoundedVariationOn (f i) (Icc a b) ∧
        variationOnFromTo (f i) Set.univ a b ≤ (M : ℝ) * B i := by
  obtain ⟨M, hM⟩ := published_uniform_common_monotone_partition
    (ι := ι) hCell hHardt hQE hMono G hG
  refine ⟨M, ?_⟩
  intro p f a b B hab hf hrep hB
  obtain ⟨n, t, hn, ht0, htn, ht, hm⟩ := hM p f a b hab hf hrep
  have h := family_variation_le_of_bounded_common_partition f B M t n hn ht
    (by simpa only [ht0, htn] using hf) hm (by simpa only [ht0, htn] using hB)
  simpa only [ht0, htn] using h

end PaperI
