import PaperILean.SampleMinorVolume

/-! The whole class of phase-dependent certificates is controlled using one
actual certificate chosen per fixed reference class, before any phase is tested.
The reference maps need not have a selected minor. No measurability of the
uncountable certificate projection is assumed or needed for this outer bound. -/
noncomputable section
open scoped BigOperators ENNReal
open Set MeasureTheory
namespace PaperI.FiniteSampleEnvelope

/-- A full all-choice envelope: every eligible witness is included. -/
def comparisonEnvelope {ι κ Q Ω : Type*} [Fintype ι] [Fintype κ]
    (A : Ω → (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (eligible : Q → Ω → Prop) (W : ℝ) :
    Set (ι → ℝ) :=
  {x | ∃ q w, eligible q w ∧ coordinateL2Norm (A w x) ≤ W}

/-- One good actual minor per nonempty fixed class controls all allowed
phase-dependent witnesses in that class. All-G comparisons are essential. -/
theorem finite_comparison_envelope_bound
    {ι κ Q Ω : Type*} [Fintype ι] [Fintype κ] [Fintype Q]
    (A : Ω → (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (R : Q → (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (minor : Ω → (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (eligible : Q → Ω → Prop) (Δ B D W : ℝ)
    (hΔ : 0 < Δ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hdet : ∀ q w, eligible q w → Δ ≤ |LinearMap.det (minor w)|)
    (hupper : ∀ q w, eligible q w → ∀ x,
      coordinateL2Norm (A w x) ≤ B * coordinateL2Norm (R q x))
    (hlower : ∀ q w, eligible q w → ∀ x,
      coordinateL2Norm (R q x) ≤ B * coordinateL2Norm (A w x))
    (hminor : ∀ q w, eligible q w → ∀ x i,
      |minor w x i| ≤ D * coordinateL2Norm (A w x)) :
    volume (comparisonEnvelope A eligible W) ≤
      (Fintype.card Q : ℝ≥0∞) *
        ENNReal.ofReal (Δ⁻¹ * (2*(D*B*B*W))^(Fintype.card ι)) := by
  classical
  let S : Q → Set (ι → ℝ) := fun q =>
    {x | ∃ w, eligible q w ∧ coordinateL2Norm (A w x) ≤ W}
  have hS (q : Q) : volume (S q) ≤
      ENNReal.ofReal (Δ⁻¹ * (2*(D*B*B*W))^(Fintype.card ι)) := by
    by_cases he : ∃ w, eligible q w
    · obtain ⟨w₀, hw₀⟩ := he
      have hs : S q ⊆ {x | ∀ i, |minor w₀ x i| ≤ D*B*B*W} := by
        rintro x ⟨w,hw,hx⟩ i
        calc
          |minor w₀ x i| ≤ D * coordinateL2Norm (A w₀ x) := hminor q w₀ hw₀ x i
          _ ≤ D * (B * coordinateL2Norm (R q x)) :=
            mul_le_mul_of_nonneg_left (hupper q w₀ hw₀ x) hD
          _ ≤ D * (B * (B * coordinateL2Norm (A w x))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hlower q w hw x) hB) hD
          _ ≤ D * (B * (B * W)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx hB) hB) hD
          _ = D*B*B*W := by ring
      exact (measure_mono hs).trans
        (SampleMinorVolume.linear_box_volume_le (minor w₀) Δ (D*B*B*W)
          hΔ (hdet q w₀ hw₀) (by positivity))
    · have hs : S q = ∅ := by
        ext x
        simp only [S, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨w,hw,_⟩
        exact he ⟨w,hw⟩
      rw [hs,measure_empty]
      exact zero_le _
  have hEq : comparisonEnvelope A eligible W = ⋃ q, S q := by
    ext x
    simp only [comparisonEnvelope,S,mem_setOf_eq,mem_iUnion]
  rw [hEq]
  calc
    volume (⋃ q, S q) ≤ ∑ q, volume (S q) := measure_iUnion_fintype_le volume S
    _ ≤ ∑ _q : Q, ENNReal.ofReal (Δ⁻¹*(2*(D*B*B*W))^(Fintype.card ι)) :=
      Finset.sum_le_sum (fun q _ => hS q)
    _ = _ := by simp

end PaperI.FiniteSampleEnvelope
