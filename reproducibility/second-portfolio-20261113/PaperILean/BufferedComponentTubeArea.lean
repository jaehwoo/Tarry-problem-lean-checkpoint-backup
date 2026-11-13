import PaperILean.BufferedComponentLocalization
import PaperILean.UniformLocalFrontierTube

/-! I1261: apply the original arclength/square bound to the actual component
and its local-width enlargement. The format constant precedes even the
nonnegative enlargement factor, whose dependence is displayed explicitly. -/

noncomputable section
namespace PaperI
open Set Metric MeasureTheory

theorem published_uniform_bufferedComponent_enlargement_area
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hMono : PublishedOneVariableMonotonicity)
    (s D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Set (EuclideanSpace ℝ (Fin 2)))
      (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) →
      IsOpen E → Bornology.IsBounded E → ∀ (b W : ℝ), 0 ≤ b → 0 < W →
      ∀ z : EuclideanSpace ℝ (Fin 2),
      volume (cthickening (b*W) (bufferedBandComponent E W z)) ≤
        ENNReal.ofReal (K*(b+5)*(b+4)*bufferedComponentScale E W z*W) := by
  obtain ⟨K,hK,harea⟩ := published_uniform_original_localFrontier_tube_area
    hCAD hCell hHardt hQE hMono s D
  refine ⟨K/4,by positivity,?_⟩
  intro E A hc hd hA ho hb b W hb0 hW z
  by_cases hz : z ∈ bufferedDistanceBand E W
  · have hL := bufferedComponentScale_pos E hW z
    have hWL : W ≤ bufferedComponentScale E W z := le_max_left _ _
    have hsmall : 0 < (b+4)*W/4 := by positivity
    have hlarge : (b+4)*W/4 ≤ (b+5)*bufferedComponentScale E W z := by
      have hmul := mul_le_mul_of_nonneg_left hWL (show 0 ≤ b+4 by linarith)
      nlinarith
    have h := (harea E A hc hd hA ho z ((b+5)*bufferedComponentScale E W z)
      ((b+4)*W/4) hsmall hlarge).1
    have hsub := bufferedBandComponent_scaled_enlargement_localization hb hW hb0
      (mem_bufferedBandComponent hz)
    calc
      _ ≤ volume (cthickening ((b+4)*W)
          (frontier E ∩ closedBall z ((b+5)*bufferedComponentScale E W z))) := measure_mono hsub
      _ ≤ ENNReal.ofReal (K*((b+5)*bufferedComponentScale E W z)*((b+4)*W/4)) := by
        convert h using 1 <;> congr 2 <;> ring
      _ = _ := by congr 1; ring
  · have he : bufferedBandComponent E W z = ∅ := connectedComponentIn_eq_empty hz
    simp only [he,cthickening_empty,measure_empty,zero_le]

theorem published_uniform_bufferedComponent_area
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hMono : PublishedOneVariableMonotonicity)
    (s D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Set (EuclideanSpace ℝ (Fin 2)))
      (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) →
      IsOpen E → Bornology.IsBounded E → ∀ W : ℝ, 0 < W →
      ∀ z : EuclideanSpace ℝ (Fin 2),
      volume (closure (bufferedBandComponent E W z)) ≤
        ENNReal.ofReal (K*bufferedComponentScale E W z*W) ∧
      volume (bufferedBandComponent E W z) ≤
        ENNReal.ofReal (K*bufferedComponentScale E W z*W) := by
  obtain ⟨K,hK,harea⟩ := published_uniform_bufferedComponent_enlargement_area
    hCAD hCell hHardt hQE hMono s D
  refine ⟨K*20,by positivity,?_⟩
  intro E A hc hd hA ho hb W hW z
  have h := harea E A hc hd hA ho hb 0 W le_rfl hW z
  simp only [zero_mul,cthickening_zero,zero_add] at h
  have hc' : volume (closure (bufferedBandComponent E W z)) ≤
      ENNReal.ofReal (K*20*bufferedComponentScale E W z*W) := by
    convert h using 1 <;> congr 1 <;> ring
  exact ⟨hc',(measure_mono subset_closure).trans hc'⟩

end PaperI
