import PaperILean.RotationGroupTopology

/-! I327/331: a fixed open exponential chart on the exact rotation group.
Source radius one half and both maps are independent of e,t,F,R. The image is
open relative to SO(3), not in the nine-dimensional ambient matrix space. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm Topology
namespace PaperI

def rotationChartSource : Set PhysicalSpace := {x | ‖skewMatrixOfCoordinates x‖ < 1/2}

def rotationChartTarget : Set rotationGroup3 :=
  {O | ‖rotationMatrix O-1‖ < 1 ∧ ‖rotationLogSeries O‖ < 1/2}

theorem rotationChartSource_isOpen : IsOpen rotationChartSource :=
  isOpen_lt skewMatrixOfCoordinates_continuous.norm continuous_const

theorem rotationChartTarget_isOpen : IsOpen rotationChartTarget := by
  have hdom : IsOpen {O : rotationGroup3 | ‖rotationMatrix O-1‖ < 1} :=
    isOpen_lt (rotationMatrix_continuous.sub continuous_const).norm continuous_const
  have hc : ContinuousOn (fun O => ‖rotationLogSeries O‖)
      {O : rotationGroup3 | ‖rotationMatrix O-1‖ < 1} :=
    fun O hO => (rotationLogSeries_continuousAt O hO).norm.continuousWithinAt
  exact hc.isOpen_inter_preimage hdom isOpen_Iio

theorem rotationLogSeries_skew_on_chartTarget (O : rotationGroup3)
    (hO : O ∈ rotationChartTarget) : (rotationLogSeries O)ᵀ = -rotationLogSeries O := by
  have hdomi : ‖rotationMatrix O⁻¹-1‖ < 1 := by
    rw [rotationMatrix_inv, ← Matrix.transpose_one, ← Matrix.transpose_sub,
      matrix_l2_opNorm_transpose]
    exact hO.1
  have htrans : rotationLogSeries O⁻¹ = (rotationLogSeries O)ᵀ := by
    unfold rotationLogSeries
    rw [rotationMatrix_inv]
    exact (matrixLogSeries_transpose _ hO.1).symm
  have hsmalli : ‖rotationLogSeries O⁻¹‖ < 1/2 := by
    rw [htrans, matrix_l2_opNorm_transpose]
    exact hO.2
  have hAB : rotationMatrix O*rotationMatrix O⁻¹ = 1 := by
    rw [← rotationMatrix_mul, mul_inv_cancel, rotationMatrix_one]
  exact htrans.symm.trans (matrixLogSeries_inverse_eq_neg_of_log_small _ _ hAB
    hO.1 hdomi hO.2 hsmalli)

theorem rotationCoordinateLog_coordinateExp (x : PhysicalSpace)
    (hx : x ∈ rotationChartSource) : rotationCoordinateLog (rotationCoordinateExp x) = x := by
  unfold rotationCoordinateLog rotationLogSeries
  rw [rotationMatrix_coordinateExp, matrixLogSeries_exp _ hx]
  exact skewCoordinatesOfMatrix_left_inverse x

theorem rotationCoordinateExp_coordinateLog (O : rotationGroup3)
    (hO : O ∈ rotationChartTarget) : rotationCoordinateExp (rotationCoordinateLog O) = O := by
  apply rotationMatrix_injective
  rw [rotationMatrix_coordinateExp]
  unfold rotationCoordinateLog
  rw [skewMatrixOfCoordinates_right_inverse _ (rotationLogSeries_skew_on_chartTarget O hO)]
  exact matrix_exp_matrixLogSeries _ hO.1

theorem rotationCoordinateExp_mapsTo_chart :
    MapsTo rotationCoordinateExp rotationChartSource rotationChartTarget := by
  intro x hx
  constructor
  · rw [rotationMatrix_coordinateExp]
    exact matrix_exp_sub_one_norm_lt_one_of_lt_half _ hx
  · change ‖matrixLogSeries (rotationMatrix (rotationCoordinateExp x))‖ < 1/2
    rw [rotationMatrix_coordinateExp, matrixLogSeries_exp _ hx]
    exact hx

theorem rotationCoordinateLog_mapsTo_chart :
    MapsTo rotationCoordinateLog rotationChartTarget rotationChartSource := by
  intro O hO
  change ‖skewMatrixOfCoordinates (skewCoordinatesOfMatrix (rotationLogSeries O))‖ < 1/2
  rw [skewMatrixOfCoordinates_right_inverse _ (rotationLogSeries_skew_on_chartTarget O hO)]
  exact hO.2

theorem rotationCoordinateLog_continuousOn_chart :
    ContinuousOn rotationCoordinateLog rotationChartTarget :=
  fun O hO => (rotationCoordinateLog_continuousAt O hO.1).continuousWithinAt

def rotationExponentialChart : PartialHomeomorph PhysicalSpace rotationGroup3 where
  toFun := rotationCoordinateExp
  invFun := rotationCoordinateLog
  source := rotationChartSource
  target := rotationChartTarget
  map_source' := rotationCoordinateExp_mapsTo_chart
  map_target' := rotationCoordinateLog_mapsTo_chart
  left_inv' := rotationCoordinateLog_coordinateExp
  right_inv' := rotationCoordinateExp_coordinateLog
  open_source := rotationChartSource_isOpen
  open_target := rotationChartTarget_isOpen
  continuousOn_toFun := rotationCoordinateExp_continuous.continuousOn
  continuousOn_invFun := rotationCoordinateLog_continuousOn_chart

theorem rotationCoordinateExp_image_chartSource :
    rotationCoordinateExp '' rotationChartSource = rotationChartTarget :=
  rotationExponentialChart.image_source_eq_target

theorem rotationCoordinateExp_injOn_chart : InjOn rotationCoordinateExp rotationChartSource :=
  rotationExponentialChart.injOn

theorem rotationCoordinateLog_injOn_chart : InjOn rotationCoordinateLog rotationChartTarget :=
  rotationExponentialChart.symm.injOn

theorem zero_mem_rotationChartSource : (0 : PhysicalSpace) ∈ rotationChartSource := by
  simp [rotationChartSource, skewMatrixOfCoordinates_zero]

theorem one_mem_rotationChartTarget : (1 : rotationGroup3) ∈ rotationChartTarget := by
  simp [rotationChartTarget, rotationMatrix_one, rotationLogSeries_one]

theorem rotationChartTarget_mem_nhds : rotationChartTarget ∈ 𝓝 (1 : rotationGroup3) :=
  rotationChartTarget_isOpen.mem_nhds one_mem_rotationChartTarget

theorem rotationNeighborhood_subset_chartTarget
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10) :
    rotationNeighborhood (positiveDiagonalFrame e he) t ⊆ rotationChartTarget := by
  intro O hO
  exact ⟨rotationNeighborhood_source_ordinary_domain e he t ht O hO,
    rotationLogSeries_source_norm_lt_half e he t ht O hO⟩

theorem skewCoordinateBall_subset_chartSource
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10) :
    skewCoordinateBall e ((10/9)*t) ⊆ rotationChartSource := by
  intro x hx
  exact anisotropicSkewBall_source_fixed_radius e he t ht _
    ⟨skewMatrixOfCoordinates_skew x, hx⟩

end PaperI
