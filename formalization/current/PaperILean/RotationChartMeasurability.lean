import PaperILean.RotationExponentialChart

/-! I331: Borel measurability of the fixed chart, its images, and the source
anisotropic comparison in actual coordinate sets. No measure equality or Haar
density is inferred from these topological facts. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem rotationChartSource_measurableSet : MeasurableSet rotationChartSource :=
  rotationChartSource_isOpen.measurableSet

theorem rotationChartTarget_measurableSet : MeasurableSet rotationChartTarget :=
  rotationChartTarget_isOpen.measurableSet

theorem rotationCoordinateExp_measurable : Measurable rotationCoordinateExp :=
  rotationCoordinateExp_continuous.measurable

theorem rotationCoordinateExp_restrict_measurableEmbedding :
    MeasurableEmbedding (fun x : rotationChartSource => rotationCoordinateExp x) :=
  rotationExponentialChart.isOpenEmbedding_restrict.measurableEmbedding

theorem rotationCoordinateLog_restrict_measurableEmbedding :
    MeasurableEmbedding (fun O : rotationChartTarget => rotationCoordinateLog O) :=
  rotationExponentialChart.symm.isOpenEmbedding_restrict.measurableEmbedding

theorem rotationCoordinateExp_image_measurableSet (A : Set PhysicalSpace)
    (hA : MeasurableSet A) (hsub : A ⊆ rotationChartSource) :
    MeasurableSet (rotationCoordinateExp '' A) := by
  have h := rotationCoordinateExp_restrict_measurableEmbedding.measurableSet_image.mpr
    (hA.preimage measurable_subtype_coe)
  convert h using 1
  ext O
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, rfl⟩

theorem rotationCoordinateLog_image_measurableSet (A : Set rotationGroup3)
    (hA : MeasurableSet A) (hsub : A ⊆ rotationChartTarget) :
    MeasurableSet (rotationCoordinateLog '' A) := by
  have h := rotationCoordinateLog_restrict_measurableEmbedding.measurableSet_image.mpr
    (hA.preimage measurable_subtype_coe)
  convert h using 1
  ext x
  constructor
  · rintro ⟨O, hO, rfl⟩
    exact ⟨⟨O, hsub hO⟩, hO, rfl⟩
  · rintro ⟨O, hO, rfl⟩
    exact ⟨O.val, hO, rfl⟩

theorem rotationCoordinateExp_image_skewBall_subset_neighborhood
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t ≤ 1) :
    rotationCoordinateExp '' skewCoordinateBall e (t/2) ⊆
      rotationNeighborhood (positiveDiagonalFrame e he) t := by
  rintro O ⟨x, hx, rfl⟩
  exact skewRotationExp_mem_neighborhood _ _ (skewMatrixOfCoordinates_skew x) t ht hx

theorem rotationCoordinateLog_image_neighborhood_subset_skewBall
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10) :
    rotationCoordinateLog '' rotationNeighborhood (positiveDiagonalFrame e he) t ⊆
      skewCoordinateBall e ((10/9)*t) := by
  rintro x ⟨O, hO, rfl⟩
  change ‖diagonalFrameConjugate e
    (skewMatrixOfCoordinates (skewCoordinatesOfMatrix (rotationLogSeries O)))‖ < (10/9)*t
  rw [skewMatrixOfCoordinates_right_inverse _ (rotationLogSeries_skew e he t ht O hO)]
  exact rotationLogSeries_conjugate_norm_lt_ten_ninths e he t ht O hO

theorem rotationNeighborhood_subset_coordinateExp_image_skewBall
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10) :
    rotationNeighborhood (positiveDiagonalFrame e he) t ⊆
      rotationCoordinateExp '' skewCoordinateBall e ((10/9)*t) := by
  intro O hO
  exact ⟨rotationCoordinateLog O,
    rotationCoordinateLog_image_neighborhood_subset_skewBall e he t ht ⟨O, hO, rfl⟩,
    rotationCoordinateExp_coordinateLog O (rotationNeighborhood_subset_chartTarget e he t ht hO)⟩

theorem rotationCoordinateExp_image_skewBall_measurableSet
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10) :
    MeasurableSet (rotationCoordinateExp '' skewCoordinateBall e ((10/9)*t)) :=
  rotationCoordinateExp_image_measurableSet _ (skewCoordinateBall_measurableSet e _)
    (skewCoordinateBall_subset_chartSource e he t ht)

theorem rotationCoordinateLog_image_neighborhood_measurableSet
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10) :
    MeasurableSet (rotationCoordinateLog '' rotationNeighborhood (positiveDiagonalFrame e he) t) :=
  rotationCoordinateLog_image_measurableSet _ (rotationNeighborhood_measurableSet _ _)
    (rotationNeighborhood_subset_chartTarget e he t ht)

end PaperI
