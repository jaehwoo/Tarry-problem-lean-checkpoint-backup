import PaperILean.PortfolioAtlasOverlap
import PaperILean.ProjectedPackingCount

/-! The entire projected-packing proposition I3279-I3310, from its stated
continued normalization family and original indexed packing hypothesis.
The exponent below is fixed before all P-dependent polynomial and family data.
The outer set may retain arbitrary additional coefficient and physical restrictions. -/
noncomputable section
open scoped BigOperators ENNReal Matrix.L2OpNorm
namespace PaperI.PortfolioAtlasStage

open Set Classical MeasureTheory ProjectedParallelogramArea ProjectedContinuedFrameCount
open ProjectedNormalizationRightFactors ExceptionalFiberPackingStage

/-- The whole projected-packing count from the original actual normalized
continuations. Initial quantitative coefficient/pivot bounds are not needed
again once the source explicitly supplies these continuations and their bounds.
No normalization-existence, overlap, projected-area or final-count conclusion
is added as a hypothesis. Repeated labels and infinite outer area are retained. -/
theorem projected_packing_from_regular_normalization
    (D : ℕ) (C a : ℝ)
    (G : MvPolynomial (Fin 3) ℝ) (hdegree : G.totalDegree ≤ D)
    (P r Λ : ℝ) (hP : 2 ≤ P) (hΛ : 0 ≤ Λ) (hr : P ^ (-C) ≤ r)
    (n : ℕ) (N : Set (Fin 6 → ℝ))
    (g k : Fin n → Fin 6 → ℝ) (u : Fin n → (ℝ × ℝ) → Fin 6 → ℝ)
    (hcoords : ∀ i p, p ∈ square r → u i p 4 = p.1 ∧ u i p 5 = p.2)
    (hcontinue : ∀ i p, p ∈ square r →
      originalUpperAffineComp (originalUpperAffineComp (g i) (k i)) (u i p) ∈ N)
    (hbound : ∀ i p, p ∈ square r →
      ‖homogeneous (k i)‖ ≤ P ^ C ∧
      ‖homogeneous (originalUpperAffineInv (k i))‖ ≤ P ^ C ∧
      ‖homogeneous (u i p)‖ ≤ P ^ C ∧
      ‖homogeneous (originalUpperAffineInv (u i p))‖ ≤ P ^ C)
    (hpacking : ∀ i M, 2 ≤ M →
      ((Finset.univ.filter (fun j => relativeNeighborhoodRadius (g i) (g j) ≤ M)).card : ℝ) ≤
        Λ * M ^ a)
    (hnormal : ∀ v ∈ N,
      encode v ∈ NormalFibers.normalizedFrames G (v 4) (v 5)) :
    (n : ℝ≥0∞) ≤
      ENNReal.ofReal (P ^ (3 * max C ((4 * max C 0 + 3) * a) + (D : ℝ)) * Λ) *
        volume ((fun v : Fin 6 → ℝ => (v 4, v 5)) '' N) := by
  classical
  let h : Fin n → Fin 6 → ℝ := fun i => originalUpperAffineComp (g i) (k i)
  let Q : Fin n → Set (ℝ × ℝ) := fun i =>
    parallelogram (h i 4) (h i 5) (h i 3) r
  let E : Set (ℝ × ℝ) := (fun v : Fin 6 → ℝ => (v 4, v 5)) '' N
  let C1 : ℝ := max C ((4 * max C 0 + 3) * a)
  have hPpos : 0 < P := by linarith
  have hrpos : 0 < r := (Real.rpow_pos_of_pos hPpos (-C)).trans_le hr
  have hr' : P ^ (-C1) ≤ r :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ P)
      (neg_le_neg (le_max_left C ((4 * max C 0 + 3) * a)))).trans hr
  have hQ (i : Fin n) : MeasurableSet (Q i) := parallelogram_measurable _ _ _ _
  have harea (i : Fin n) : volume (Q i) = ENNReal.ofReal (4 * r ^ 2) :=
    parallelogram_volume _ _ _ _ hrpos.le
  have hsub (i : Fin n) : Q i ⊆ E :=
    (ProjectedNormalizationProjection.projected_normalization_projection_stage
      n N r h u hcoords hcontinue i).2
  have hoverReal := PortfolioAtlasOverlap.indexed_overlap G D hdegree C P a Λ r
    hP hΛ hrpos n N g k u hcoords hcontinue hbound hpacking hnormal
  have hover (x : ℝ × ℝ) (_hx : x ∈ E) :
      (∑ i, (Q i).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤
        ENNReal.ofReal (3 * (D : ℝ) * P ^ C1 * Λ) := by
    have hpower : P ^ ((4 * max C 0 + 3) * a) ≤ P ^ C1 :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ P)
        (le_max_right C ((4 * max C 0 + 3) * a))
    have hcard : ((Finset.univ.filter (fun i => x ∈ Q i)).card : ℝ) ≤
        3 * (D : ℝ) * P ^ C1 * Λ := by
      apply (hoverReal x).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower (by positivity)) hΛ
    have he := ENNReal.ofReal_le_ofReal hcard
    simpa only [Set.indicator_apply, Finset.sum_boole, ENNReal.ofReal_natCast] using he
  exact (ProjectedPackingCount.projected_packing_count_stage D C1 P r Λ hP hΛ hr'
    n E Q hQ hsub harea hover).2.2.2

end PaperI.PortfolioAtlasStage
