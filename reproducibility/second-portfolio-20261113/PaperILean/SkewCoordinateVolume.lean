import PaperILean.AnisotropicSkewBounds

/-! I329-331: exact Euclidean volume of the weighted skew-coordinate box,
and uniform volume bounds for the linearized anisotropic skew ball.
These are coordinate Lebesgue volumes, not Haar measures on SO(3).
The logarithm/exponential chart and its Haar density are not assumed here. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def skewMatrixOfCoordinates (x : PhysicalSpace) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, x 0, x 1; -x 0, 0, x 2; -x 1, -x 2, 0]

def skewCoordinatesOfMatrix (H : Matrix (Fin 3) (Fin 3) ℝ) : PhysicalSpace :=
  ![H 0 1, H 0 2, H 1 2]

theorem skewMatrixOfCoordinates_skew (x : PhysicalSpace) :
    (skewMatrixOfCoordinates x)ᵀ = -skewMatrixOfCoordinates x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewMatrixOfCoordinates]

theorem skewCoordinatesOfMatrix_left_inverse (x : PhysicalSpace) :
    skewCoordinatesOfMatrix (skewMatrixOfCoordinates x) = x := by
  ext i
  fin_cases i <;> rfl

theorem skewMatrixOfCoordinates_right_inverse (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : Hᵀ = -H) : skewMatrixOfCoordinates (skewCoordinatesOfMatrix H) = H := by
  have h (i j : Fin 3) : H j i = -H i j :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i j) hH
  ext i j
  fin_cases i <;> fin_cases j
  · exact (skew_matrix_diagonal_zero H hH 0).symm
  · rfl
  · rfl
  · exact (h 0 1).symm
  · exact (skew_matrix_diagonal_zero H hH 1).symm
  · rfl
  · exact (h 0 2).symm
  · exact (h 1 2).symm
  · exact (skew_matrix_diagonal_zero H hH 2).symm

def skewCoordinateRadii (e : Fin 3 → ℝ) (t : ℝ) : PhysicalSpace :=
  ![t * min (e 0 / e 1) (e 1 / e 0),
    t * min (e 0 / e 2) (e 2 / e 0),
    t * min (e 1 / e 2) (e 2 / e 1)]

def skewCoordinateBox (e : Fin 3 → ℝ) (t : ℝ) : Set PhysicalSpace :=
  Icc (-skewCoordinateRadii e t) (skewCoordinateRadii e t)

theorem mem_skewCoordinateBox_iff (e : Fin 3 → ℝ) (t : ℝ) (x : PhysicalSpace) :
    x ∈ skewCoordinateBox e t ↔ ∀ i, |x i| ≤ skewCoordinateRadii e t i := by
  constructor
  · rintro ⟨hl, hu⟩ i
    exact abs_le.mpr ⟨hl i, hu i⟩
  · intro h
    exact ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩

theorem skewMatrixOfCoordinates_mem_box_iff (e : Fin 3 → ℝ) (t : ℝ) (x : PhysicalSpace) :
    skewMatrixOfCoordinates x ∈ anisotropicSkewBox e t ↔ x ∈ skewCoordinateBox e t := by
  rw [mem_skewCoordinateBox_iff]
  constructor
  · intro h i
    fin_cases i
    · exact h.2 0 1 (by decide)
    · exact h.2 0 2 (by decide)
    · exact h.2 1 2 (by decide)
  · intro h
    refine ⟨skewMatrixOfCoordinates_skew x, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · exact h 0
    · exact h 1
    · exact h 2

theorem skewCoordinateRadii_nonneg (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) : 0 ≤ skewCoordinateRadii e t i := by
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  fin_cases i <;> dsimp [skewCoordinateRadii] <;> positivity

theorem skewCoordinateBox_measurableSet (e : Fin 3 → ℝ) (t : ℝ) :
    MeasurableSet (skewCoordinateBox e t) := isClosed_Icc.measurableSet

theorem skewCoordinateBox_volume (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : 0 ≤ t) :
    physicalMeasure (skewCoordinateBox e t) = ENNReal.ofReal
      (8 * t^3 * min (e 0 / e 1) (e 1 / e 0) * min (e 0 / e 2) (e 2 / e 0) *
        min (e 1 / e 2) (e 2 / e 1)) := by
  rw [physicalMeasure_eq_volume, skewCoordinateBox, Real.volume_Icc_pi, Fin.prod_univ_three]
  simp only [Pi.neg_apply, sub_neg_eq_add, ← two_mul]
  have h0 := skewCoordinateRadii_nonneg e he t ht 0
  have h1 := skewCoordinateRadii_nonneg e he t ht 1
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * skewCoordinateRadii e t 0),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * skewCoordinateRadii e t 0) * (2 * skewCoordinateRadii e t 1))]
  congr 1
  dsimp [skewCoordinateRadii]
  ring

theorem skewCoordinateBox_volume_ordered (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (h01 : e 0 ≤ e 1) (h12 : e 1 ≤ e 2) (t : ℝ) (ht : 0 ≤ t) :
    physicalMeasure (skewCoordinateBox e t) =
      ENNReal.ofReal (8 * t^3 * (e 0 / e 2)^2) := by
  rw [skewCoordinateBox_volume e he t ht,
    min_eq_left (ordered_positive_ratio_le_reverse _ _ (he 0) (he 1) h01),
    min_eq_left (ordered_positive_ratio_le_reverse _ _ (he 0) (he 2) (h01.trans h12)),
    min_eq_left (ordered_positive_ratio_le_reverse _ _ (he 1) (he 2) h12)]
  congr 1
  field_simp [(he 0).ne', (he 1).ne', (he 2).ne']
  <;> ring

def skewCoordinateBall (e : Fin 3 → ℝ) (t : ℝ) : Set PhysicalSpace :=
  {x | ‖diagonalFrameConjugate e (skewMatrixOfCoordinates x)‖ < t}

theorem skewCoordinateBall_isOpen (e : Fin 3 → ℝ) (t : ℝ) :
    IsOpen (skewCoordinateBall e t) := by
  apply isOpen_lt _ continuous_const
  have hc : Continuous skewMatrixOfCoordinates := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_apply 0
    · exact continuous_apply 1
    · exact (continuous_apply 0).neg
    · exact continuous_const
    · exact continuous_apply 2
    · exact (continuous_apply 1).neg
    · exact (continuous_apply 2).neg
    · exact continuous_const
  exact ((continuous_const.mul hc).mul continuous_const).norm

theorem skewCoordinateBall_measurableSet (e : Fin 3 → ℝ) (t : ℝ) :
    MeasurableSet (skewCoordinateBall e t) := (skewCoordinateBall_isOpen e t).measurableSet

theorem skewCoordinateBall_subset_box (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) :
    skewCoordinateBall e t ⊆ skewCoordinateBox e t := by
  intro x hx
  apply (skewMatrixOfCoordinates_mem_box_iff e t x).mp
  exact anisotropicSkewBall_subset_box e he t ⟨skewMatrixOfCoordinates_skew x, hx⟩

theorem skewCoordinateBox_quarter_subset_ball (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (t : ℝ) (ht : 0 < t) : skewCoordinateBox e (t/4) ⊆ skewCoordinateBall e t := by
  intro x hx
  exact (anisotropicSkewBox_quarter_subset_ball e he t ht
    ((skewMatrixOfCoordinates_mem_box_iff e (t/4) x).mpr hx)).2

theorem skewCoordinateBall_volume_bounds (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (h01 : e 0 ≤ e 1) (h12 : e 1 ≤ e 2) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal ((t^3 / 8) * (e 0 / e 2)^2) ≤ physicalMeasure (skewCoordinateBall e t) ∧
      physicalMeasure (skewCoordinateBall e t) ≤ ENNReal.ofReal (8 * t^3 * (e 0 / e 2)^2) := by
  have hl := measure_mono (μ := physicalMeasure) (skewCoordinateBox_quarter_subset_ball e he t ht)
  have hu := measure_mono (μ := physicalMeasure) (skewCoordinateBall_subset_box e he t)
  rw [skewCoordinateBox_volume_ordered e he h01 h12 (t/4) (by positivity)] at hl
  rw [skewCoordinateBox_volume_ordered e he h01 h12 t ht.le] at hu
  refine ⟨?_, hu⟩
  convert hl using 1
  congr 1
  ring

theorem skewCoordinateBall_volume_positive_finite (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i)
    (h01 : e 0 ≤ e 1) (h12 : e 1 ≤ e 2) (t : ℝ) (ht : 0 < t) :
    0 < physicalMeasure (skewCoordinateBall e t) ∧
      physicalMeasure (skewCoordinateBall e t) < ⊤ := by
  obtain ⟨hl, hu⟩ := skewCoordinateBall_volume_bounds e he h01 h12 t ht
  have hr : 0 < e 0 / e 2 := div_pos (he 0) (he 2)
  exact ⟨(ENNReal.ofReal_pos.mpr (by positivity : 0 < (t^3 / 8) * (e 0 / e 2)^2)).trans_le hl,
    hu.trans_lt ENNReal.ofReal_lt_top⟩

end PaperI
