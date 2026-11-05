import PaperILean.RotationHaarIdentification

/-! I331: the uniform anisotropic Haar-volume estimate for the unchanged U_E(t).
All constants are chosen before e,t,F,R and side ratios. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix Matrix.L2OpNorm
namespace PaperI

theorem skewCoordinateBall_mono (e : Fin 3 → ℝ) {s t : ℝ} (hst : s ≤ t) :
    skewCoordinateBall e s ⊆ skewCoordinateBall e t := fun _ hx => hx.trans_le hst

theorem rotationHaarMeasure_diagonal_neighborhood_bounds :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i),
      e 0 ≤ e 1 → e 1 ≤ e 2 → ∀ t : ℝ, 0 < t → t < 1/10 →
        ENNReal.ofReal (c * t^3 * (e 0 / e 2)^2) ≤
          rotationHaarMeasure (rotationNeighborhood (positiveDiagonalFrame e he) t) ∧
        rotationHaarMeasure (rotationNeighborhood (positiveDiagonalFrame e he) t) ≤
          ENNReal.ofReal (C * t^3 * (e 0 / e 2)^2) := by
  obtain ⟨c, C, hc, hcC, hb⟩ := rotationHaarMeasure_uniform_source_bounds
  refine ⟨c / 64, (8000/729) * C, by positivity, ?_, ?_⟩
  · nlinarith
  intro e he h01 h12 t ht0 ht
  have hsmall : t/2 ≤ (10/9)*t := by linarith
  have hlow := hb e he t ht (skewCoordinateBall e (t/2))
    (skewCoordinateBall_measurableSet e _) (skewCoordinateBall_mono e hsmall)
  have hupp := hb e he t ht (skewCoordinateBall e ((10/9)*t))
    (skewCoordinateBall_measurableSet e _) Subset.rfl
  have vl := (skewCoordinateBall_volume_bounds e he h01 h12 (t/2) (by positivity)).1
  have vu := (skewCoordinateBall_volume_bounds e he h01 h12 ((10/9)*t) (by positivity)).2
  constructor
  · calc
      ENNReal.ofReal (c / 64 * t^3 * (e 0 / e 2)^2) =
          ENNReal.ofReal c * ENNReal.ofReal (((t/2)^3 / 8) * (e 0 / e 2)^2) := by
            rw [← ENNReal.ofReal_mul hc.le]
            congr 1
            ring
      _ ≤ ENNReal.ofReal c * physicalMeasure (skewCoordinateBall e (t/2)) :=
        mul_le_mul_left' vl _
      _ ≤ rotationHaarMeasure (rotationCoordinateExp '' skewCoordinateBall e (t/2)) := hlow.1
      _ ≤ rotationHaarMeasure (rotationNeighborhood (positiveDiagonalFrame e he) t) :=
        measure_mono (rotationCoordinateExp_image_skewBall_subset_neighborhood e he t (by linarith))
  · calc
      rotationHaarMeasure (rotationNeighborhood (positiveDiagonalFrame e he) t) ≤
          rotationHaarMeasure (rotationCoordinateExp '' skewCoordinateBall e ((10/9)*t)) :=
        measure_mono (rotationNeighborhood_subset_coordinateExp_image_skewBall e he t ht)
      _ ≤ ENNReal.ofReal C * physicalMeasure (skewCoordinateBall e ((10/9)*t)) := hupp.2
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (8 * ((10/9)*t)^3 * (e 0 / e 2)^2) :=
        mul_le_mul_left' vu _
      _ = ENNReal.ofReal ((8000/729) * C * t^3 * (e 0 / e 2)^2) := by
        rw [← ENNReal.ofReal_mul (hc.le.trans hcC)]
        congr 1
        ring

theorem rotationHaarMeasure_diagonal_neighborhood_bounds_real :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i),
      e 0 ≤ e 1 → e 1 ≤ e 2 → ∀ t : ℝ, 0 < t → t < 1/10 →
        c * t^3 * (e 0 / e 2)^2 ≤
          (rotationHaarMeasure (rotationNeighborhood (positiveDiagonalFrame e he) t)).toReal ∧
        (rotationHaarMeasure (rotationNeighborhood (positiveDiagonalFrame e he) t)).toReal ≤
          C * t^3 * (e 0 / e 2)^2 := by
  obtain ⟨c, C, hc, hcC, hb⟩ := rotationHaarMeasure_diagonal_neighborhood_bounds
  refine ⟨c, C, hc, hcC, ?_⟩
  intro e he h01 h12 t ht0 ht
  obtain ⟨hl, hu⟩ := hb e he h01 h12 t ht0 ht
  have hn := (rotationHaarMeasure_neighborhood_finite (positiveDiagonalFrame e he) t).ne
  have hC : 0 ≤ C := hc.le.trans hcC
  constructor
  · simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ c * t^3 * (e 0 / e 2)^2)] using
      ENNReal.toReal_mono hn hl
  · simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ C * t^3 * (e 0 / e 2)^2)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hu

theorem rotationHaarMeasure_diagonal_neighborhood_reciprocal_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i),
      e 0 ≤ e 1 → e 1 ≤ e 2 → ∀ t : ℝ, 0 < t → t < 1/10 →
        1 / (rotationHaarMeasure (rotationNeighborhood (positiveDiagonalFrame e he) t)).toReal ≤
          (C / t^3) * (e 2 / e 0)^2 := by
  obtain ⟨c, C, hc, hcC, hb⟩ := rotationHaarMeasure_diagonal_neighborhood_bounds_real
  refine ⟨1/c, by positivity, ?_⟩
  intro e he h01 h12 t ht0 ht
  have hr : 0 < e 0 / e 2 := div_pos (he 0) (he 2)
  have hp : 0 < c * t^3 * (e 0 / e 2)^2 := by positivity
  calc
    1 / (rotationHaarMeasure (rotationNeighborhood (positiveDiagonalFrame e he) t)).toReal ≤
        1 / (c * t^3 * (e 0 / e 2)^2) :=
      one_div_le_one_div_of_le hp (hb e he h01 h12 t ht0 ht).1
    _ = ((1/c) / t^3) * (e 2 / e 0)^2 := by
      field_simp [(he 0).ne', (he 2).ne', ht0.ne', hc.ne']

end PaperI
