import PaperILean.OriginalHaarWindowMeasures
import PaperILean.OriginalHaarArbitraryPhase

/-! The final right-coset application for H in the original Haar lemma.
Actual conjugation preserves the SAME coordinate Haar normalization, and
measurable embeddings transfer outer measures of arbitrary orbit predicates.
No new Borel premise or location bound is imposed. -/
noncomputable section
namespace PaperI.OriginalHaarWindowRightCoset
open Set MeasureTheory
open HaarCosetMeasure OriginalHaarWindowMeasures OriginalHaarArbitraryPhase

private theorem embed_measurableEmbedding : MeasurableEmbedding HaarCosetMeasure.embed :=
  HaarCosetMeasure.continuous_embed.measurableEmbedding HaarCosetMeasure.embed_injective

private theorem adjoint_measurableEmbedding (a f : ℝ) :
    MeasurableEmbedding (HaarCosetMeasure.adjoint a f) := by
  exact (HaarCosetMeasure.adjointLinearEquiv a f).toLinearMap.continuous_of_finiteDimensional.measurableEmbedding
    (HaarCosetMeasure.adjointLinearEquiv a f).injective

/-- The exact domain-volume equality for every actual orbit predicate,
including nonmeasurable predicates interpreted by outer measure. -/
theorem haarH_left_right_domain_measure (g₀ : Fin 6 → ℝ) (Q : (Fin 6 → ℝ) → Prop) :
    haarH {g | g ∈ originalHaarSubgroupSet .H ∧ Q (originalUpperAffineComp g₀ g)} =
      haarH {g | g ∈ originalHaarSubgroupSet .H ∧ Q (originalUpperAffineComp g g₀)} := by
  let L : Set (Fin 6 → ℝ) := {g | g ∈ originalHaarSubgroupSet .H ∧ Q (originalUpperAffineComp g₀ g)}
  let R : Set (Fin 6 → ℝ) := {g | g ∈ originalHaarSubgroupSet .H ∧ Q (originalUpperAffineComp g g₀)}
  have hL : HaarCosetMeasure.embed ⁻¹' L =
      {u | Q (originalUpperAffineComp g₀ (HaarCosetMeasure.embed u))} := by
    ext u
    simp [L,originalHaarSubgroupSet,HaarCosetMeasure.embed]
  have hR : HaarCosetMeasure.embed ⁻¹' R =
      {u | Q (originalUpperAffineComp (HaarCosetMeasure.embed u) g₀)} := by
    ext u
    simp [R,originalHaarSubgroupSet,HaarCosetMeasure.embed]
  have hset : {u | Q (originalUpperAffineComp g₀ (HaarCosetMeasure.embed u))} =
      HaarCosetMeasure.adjoint (g₀ 0) (g₀ 5) ⁻¹'
        {u | Q (originalUpperAffineComp (HaarCosetMeasure.embed u) g₀)} := by
    ext u
    simp only [Set.mem_setOf_eq,Set.mem_preimage]
    rw [HaarCosetMeasure.actual_left_eq_right_adjoint]
  change haarH L = haarH R
  unfold haarH
  rw [embed_measurableEmbedding.map_apply,embed_measurableEmbedding.map_apply,hL,hR,hset,
    ← (adjoint_measurableEmbedding (g₀ 0) (g₀ 5)).map_apply,
    HaarCosetMeasure.adjoint_preserves_haar]

/-- The raw arbitrary-phase right-coset condition has exactly the same
transported Haar volume as the previously bounded left-coset condition. -/
theorem raw_haarH_left_right_domain_measure {k : ℕ}
    (W : Set (CoefficientSpace k)) (f : PhysicalSpace → ℝ) (g₀ : Fin 6 → ℝ) :
    haarH {g | g ∈ originalHaarSubgroupSet .H ∧ ∃ F ∈ W, ∀ x : PhysicalSpace,
      phase F x = normalizedAlong f (originalUpperAffineComp g₀ g) x} =
    haarH {g | g ∈ originalHaarSubgroupSet .H ∧ ∃ F ∈ W, ∀ x : PhysicalSpace,
      phase F x = normalizedAlong f (originalUpperAffineComp g g₀) x} :=
  haarH_left_right_domain_measure g₀ (fun g => ∃ F ∈ W, ∀ x : PhysicalSpace,
    phase F x = normalizedAlong f g x)

end PaperI.OriginalHaarWindowRightCoset
