import PaperILean.MatrixExpLogDifferential
import PaperILean.RotationChartSmoothness

/-! I327/331: the fixed chart is analytic in both directions (the inverse has
an analytic ambient extension), and has rank three throughout its source.
Uniform differential bounds on a fixed compact subregion are not Haar-density
bounds; that measure-identification obligation remains separate. -/
noncomputable section
open Set Filter
open scoped Topology Matrix Matrix.L2OpNorm
namespace PaperI

def rotationLogCoordinatesAmbient (A : Matrix (Fin 3) (Fin 3) ℝ) : PhysicalSpace :=
  skewCoordinatesOfMatrix (matrixLogSeries A)

theorem rotationCoordinateLog_eq_ambient (O : rotationGroup3) :
    rotationCoordinateLog O = rotationLogCoordinatesAmbient (rotationMatrix O) := rfl

theorem rotationLogCoordinatesAmbient_analyticAt (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ‖A-1‖ < 1) : AnalyticAt ℝ rotationLogCoordinatesAmbient A :=
  (skewCoordinatesMatrixCLM.analyticAt (matrixLogSeries A)).comp
    (matrixLogSeries_analyticAt A hA)

theorem rotationLogCoordinatesAmbient_contDiffOn :
    ContDiffOn ℝ ⊤ rotationLogCoordinatesAmbient
      {A : Matrix (Fin 3) (Fin 3) ℝ | ‖A-1‖ < 1} :=
  (show AnalyticOnNhd ℝ rotationLogCoordinatesAmbient
    {A : Matrix (Fin 3) (Fin 3) ℝ | ‖A-1‖ < 1} from
      fun A hA => rotationLogCoordinatesAmbient_analyticAt A hA).contDiffOn
        (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).uniqueDiffOn

theorem rotationLogCoordinatesAmbient_analyticAt_chart (O : rotationGroup3)
    (hO : O ∈ rotationChartTarget) :
    AnalyticAt ℝ rotationLogCoordinatesAmbient (rotationMatrix O) :=
  rotationLogCoordinatesAmbient_analyticAt _ hO.1

theorem rotationLogCoordinatesAmbient_coordinateExp (x : PhysicalSpace)
    (hx : x ∈ rotationChartSource) :
    rotationLogCoordinatesAmbient (rotationMatrix (rotationCoordinateExp x)) = x :=
  rotationCoordinateLog_coordinateExp x hx

def rotationChartDifferential (x : PhysicalSpace) :
    PhysicalSpace →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  (matrixExpDifferential (skewMatrixOfCoordinates x)).comp skewMatrixCoordinatesCLM

def rotationChartLeftInverseDifferential (x : PhysicalSpace) :
    Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] PhysicalSpace :=
  skewCoordinatesMatrixCLM.comp
    (fderiv ℝ matrixLogSeries (rotationMatrix (rotationCoordinateExp x)))

theorem rotationCoordinateExp_matrix_hasStrictFDerivAt (x : PhysicalSpace) :
    HasStrictFDerivAt (fun y => rotationMatrix (rotationCoordinateExp y))
      (rotationChartDifferential x) x :=
  (matrix_exp_hasStrictFDerivAt (skewMatrixOfCoordinates x)).comp x
    skewMatrixCoordinatesCLM.hasStrictFDerivAt

theorem rotationCoordinateExp_matrix_fderiv (x : PhysicalSpace) :
    fderiv ℝ (fun y => rotationMatrix (rotationCoordinateExp y)) x =
      rotationChartDifferential x :=
  (rotationCoordinateExp_matrix_hasStrictFDerivAt x).hasFDerivAt.fderiv

theorem rotationLogCoordinatesAmbient_hasStrictFDerivAt (x : PhysicalSpace)
    (hx : x ∈ rotationChartSource) :
    HasStrictFDerivAt rotationLogCoordinatesAmbient (rotationChartLeftInverseDifferential x)
      (rotationMatrix (rotationCoordinateExp x)) :=
  skewCoordinatesMatrixCLM.hasStrictFDerivAt.comp _
    (matrixLogSeries_hasStrictFDerivAt _
      (matrix_exp_sub_one_norm_lt_one_of_lt_half (skewMatrixOfCoordinates x) hx))

theorem rotationChartDifferential_leftInverse (x : PhysicalSpace)
    (hx : x ∈ rotationChartSource) :
    (rotationChartLeftInverseDifferential x).comp (rotationChartDifferential x) =
      ContinuousLinearMap.id ℝ PhysicalSpace := by
  ext v i
  have h := congrArg (fun L : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ =>
    L (skewMatrixOfCoordinates v)) (matrixLog_fderiv_comp_exp (skewMatrixOfCoordinates x) hx)
  change fderiv ℝ matrixLogSeries (NormedSpace.exp ℝ (skewMatrixOfCoordinates x))
    (matrixExpDifferential (skewMatrixOfCoordinates x) (skewMatrixOfCoordinates v)) =
      skewMatrixOfCoordinates v at h
  change skewCoordinatesOfMatrix (fderiv ℝ matrixLogSeries
    (NormedSpace.exp ℝ (skewMatrixOfCoordinates x))
      (matrixExpDifferential (skewMatrixOfCoordinates x) (skewMatrixOfCoordinates v))) i = v i
  rw [h]
  exact congrFun (skewCoordinatesOfMatrix_left_inverse v) i

theorem rotationChartDifferential_leftInverse_apply (x : PhysicalSpace)
    (hx : x ∈ rotationChartSource) (v : PhysicalSpace) :
    rotationChartLeftInverseDifferential x (rotationChartDifferential x v) = v :=
  congrArg (fun L : PhysicalSpace →L[ℝ] PhysicalSpace => L v)
    (rotationChartDifferential_leftInverse x hx)

theorem rotationChartDifferential_injective (x : PhysicalSpace)
    (hx : x ∈ rotationChartSource) : Function.Injective (rotationChartDifferential x) :=
  Function.LeftInverse.injective (rotationChartDifferential_leftInverse_apply x hx)

theorem rotationCoordinateExp_matrix_fderiv_injective (x : PhysicalSpace)
    (hx : x ∈ rotationChartSource) :
    Function.Injective (fderiv ℝ (fun y => rotationMatrix (rotationCoordinateExp y)) x) := by
  rw [rotationCoordinateExp_matrix_fderiv]
  exact rotationChartDifferential_injective x hx

theorem rotationChartDifferential_continuous : Continuous rotationChartDifferential := by
  have h : Continuous (matrixExpDifferential (n := 3)) :=
    continuous_iff_continuousAt.mpr (fun H => (matrixExpDifferential_analyticAt H).continuousAt)
  exact (h.comp skewMatrixOfCoordinates_continuous).clm_comp continuous_const

theorem rotationChartLeftInverseDifferential_continuousOn :
    ContinuousOn rotationChartLeftInverseDifferential rotationChartSource := by
  apply continuousOn_const.clm_comp
  intro x hx
  exact ((matrixLog_fderiv_analyticAt _
    (matrix_exp_sub_one_norm_lt_one_of_lt_half (skewMatrixOfCoordinates x) hx)).continuousAt.comp
      (f := fun y => rotationMatrix (rotationCoordinateExp y))
      (rotationCoordinateExp_matrix_analyticAt x).continuousAt).continuousWithinAt

def rotationChartCore : Set PhysicalSpace := {x | ‖skewMatrixOfCoordinates x‖ ≤ 1/3}

theorem rotationChartCore_subset_source : rotationChartCore ⊆ rotationChartSource := by
  intro x hx
  change ‖skewMatrixOfCoordinates x‖ < 1/2
  exact lt_of_le_of_lt hx (by norm_num)

theorem rotationChartSource_nhds_core (x : PhysicalSpace) (hx : x ∈ rotationChartCore) :
    rotationChartSource ∈ 𝓝 x :=
  rotationChartSource_isOpen.mem_nhds (rotationChartCore_subset_source hx)

theorem rotationChartCore_isCompact : IsCompact rotationChartCore := by
  have he : Topology.IsClosedEmbedding skewMatrixCoordinatesCLM :=
    LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr skewMatrixOfCoordinates_injective)
  convert he.isCompact_preimage
    (isCompact_closedBall (0 : Matrix (Fin 3) (Fin 3) ℝ) (1/3)) using 1
  ext x
  simp only [rotationChartCore, Set.mem_preimage, Set.mem_setOf_eq, Metric.mem_closedBall,
    dist_zero_right, skewMatrixCoordinatesCLM_apply]

theorem rotationChartDifferential_uniform_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ rotationChartCore, ∀ v : PhysicalSpace,
      ‖v‖ ≤ C * ‖rotationChartDifferential x v‖ ∧
      ‖rotationChartDifferential x v‖ ≤ C * ‖v‖ := by
  obtain ⟨a, ha⟩ := rotationChartCore_isCompact.exists_bound_of_continuousOn
    (f := rotationChartDifferential)
    rotationChartDifferential_continuous.continuousOn
  obtain ⟨b, hb⟩ := rotationChartCore_isCompact.exists_bound_of_continuousOn
    (f := rotationChartLeftInverseDifferential)
    (rotationChartLeftInverseDifferential_continuousOn.mono rotationChartCore_subset_source)
  refine ⟨1 + |a| + |b|, by positivity, ?_⟩
  intro x hx v
  have haC : a ≤ 1 + |a| + |b| := by linarith [le_abs_self a, abs_nonneg b]
  have hbC : b ≤ 1 + |a| + |b| := by linarith [le_abs_self b, abs_nonneg a]
  constructor
  · calc
      ‖v‖ = ‖rotationChartLeftInverseDifferential x (rotationChartDifferential x v)‖ :=
        congrArg norm (rotationChartDifferential_leftInverse_apply x
          (rotationChartCore_subset_source hx) v).symm
      _ ≤ ‖rotationChartLeftInverseDifferential x‖ * ‖rotationChartDifferential x v‖ :=
        (rotationChartLeftInverseDifferential x).le_opNorm _
      _ ≤ (1 + |a| + |b|) * ‖rotationChartDifferential x v‖ :=
        mul_le_mul_of_nonneg_right ((hb x hx).trans hbC) (norm_nonneg _)
  · exact ((rotationChartDifferential x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((ha x hx).trans haC) (norm_nonneg _))

theorem skewCoordinateBall_source_norm_lt_third (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : t < 1/10) (x : PhysicalSpace)
    (hx : x ∈ skewCoordinateBall e ((10/9)*t)) : ‖skewMatrixOfCoordinates x‖ < 1/3 := by
  have h := skewCoordinateBall_ordinary_norm e he ((10/9)*t) x hx
  linarith

theorem skewCoordinateBall_subset_chartCore (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : t < 1/10) :
    skewCoordinateBall e ((10/9)*t) ⊆ rotationChartCore :=
  fun x hx => (skewCoordinateBall_source_norm_lt_third e he t ht x hx).le

theorem rotationCoordinateLog_neighborhood_mem_chartCore (e : Fin 3 → ℝ)
    (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10) (O : rotationGroup3)
    (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    rotationCoordinateLog O ∈ rotationChartCore :=
  skewCoordinateBall_subset_chartCore e he t ht
    (rotationCoordinateLog_image_neighborhood_subset_skewBall e he t ht
      (Set.mem_image_of_mem _ hO))

theorem rotationChartDifferential_uniform_source_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Fin 3 → ℝ), (∀ i, 0 < e i) →
      ∀ t : ℝ, t < 1/10 → ∀ x ∈ skewCoordinateBall e ((10/9)*t), ∀ v : PhysicalSpace,
        ‖v‖ ≤ C * ‖rotationChartDifferential x v‖ ∧
        ‖rotationChartDifferential x v‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC, hbound⟩ := rotationChartDifferential_uniform_bounds
  exact ⟨C, hC, fun e he t ht x hx v =>
    hbound x (skewCoordinateBall_subset_chartCore e he t ht hx) v⟩

end PaperI
