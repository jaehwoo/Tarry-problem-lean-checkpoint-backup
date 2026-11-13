import PaperILean.RotationChartSmoothness
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! I331: compactness and one fixed probability Haar measure on the exact group.
Normalization is by the whole compact group, before any lengths or radii.
No coordinate density or quantitative anisotropic Haar-volume estimate is claimed. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem rotationMatrix_isEmbedding : Topology.IsEmbedding rotationMatrix :=
  Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal

theorem rotationMatrix_range :
    Set.range rotationMatrix = {A : Matrix (Fin 3) (Fin 3) ℝ | A*Aᵀ = 1 ∧ A.det = 1} := by
  ext A
  rw [Set.mem_range, exists_rotationMatrix_iff]
  change (A ∈ Matrix.orthogonalGroup (Fin 3) ℝ ∧ A.det = 1) ↔ _
  rw [Matrix.mem_orthogonalGroup_iff]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Set.mem_setOf_eq]

theorem rotationMatrix_range_isClosed : IsClosed (Set.range rotationMatrix) := by
  rw [rotationMatrix_range]
  exact (isClosed_eq (continuous_id.mul continuous_id.matrix_transpose) continuous_const).inter
    (isClosed_eq continuous_id.matrix_det continuous_const)

theorem rotationMatrix_norm_le_three (O : rotationGroup3) : ‖rotationMatrix O‖ ≤ 3 := by
  have hentry (i j : Fin 3) : |rotationMatrix O i j| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using entry_norm_bound_of_unitary O.val.property i j
  simpa only [mul_one] using matrix_opNorm_le_three_mul_entry_bound (rotationMatrix O) 1
    (by norm_num) hentry

theorem rotationMatrix_range_isCompact : IsCompact (Set.range rotationMatrix) := by
  apply (isCompact_closedBall (0 : Matrix (Fin 3) (Fin 3) ℝ) 3).of_isClosed_subset
    rotationMatrix_range_isClosed
  rintro A ⟨O, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using rotationMatrix_norm_le_three O

theorem rotationGroup3_compactSpace : CompactSpace rotationGroup3 := by
  constructor
  apply rotationMatrix_isEmbedding.isCompact_iff.mpr
  simpa only [Set.image_univ] using rotationMatrix_range_isCompact

attribute [instance] rotationGroup3_compactSpace

def rotationGroupPositiveCompact : PositiveCompacts rotationGroup3 :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

def rotationHaarMeasure : Measure rotationGroup3 :=
  Measure.haarMeasure rotationGroupPositiveCompact

theorem rotationHaarMeasure_isHaarMeasure : Measure.IsHaarMeasure rotationHaarMeasure :=
  inferInstanceAs (Measure.IsHaarMeasure (Measure.haarMeasure rotationGroupPositiveCompact))

attribute [instance] rotationHaarMeasure_isHaarMeasure

theorem rotationHaarMeasure_univ : rotationHaarMeasure Set.univ = 1 :=
  Measure.haarMeasure_self

theorem rotationHaarMeasure_isProbabilityMeasure : IsProbabilityMeasure rotationHaarMeasure :=
  ⟨rotationHaarMeasure_univ⟩

attribute [instance] rotationHaarMeasure_isProbabilityMeasure

theorem rotationHaarMeasure_left_invariant (O : rotationGroup3) (A : Set rotationGroup3) :
    rotationHaarMeasure ((fun P => O*P) ⁻¹' A) = rotationHaarMeasure A :=
  measure_preimage_mul rotationHaarMeasure O A

theorem rotationHaarMeasure_neighborhood_positive (E : PositiveFrame) (t : ℝ) (ht : 0 < t) :
    0 < rotationHaarMeasure (rotationNeighborhood E t) :=
  (rotationNeighborhood_isOpen E t).measure_pos rotationHaarMeasure
    ⟨1, (one_mem_rotationNeighborhood_iff E t).mpr ht⟩

theorem rotationHaarMeasure_neighborhood_finite (E : PositiveFrame) (t : ℝ) :
    rotationHaarMeasure (rotationNeighborhood E t) < ⊤ := measure_lt_top _ _

theorem rotationHaarMeasure_chart_positive : 0 < rotationHaarMeasure rotationChartTarget :=
  rotationChartTarget_isOpen.measure_pos rotationHaarMeasure ⟨1, one_mem_rotationChartTarget⟩

end PaperI
