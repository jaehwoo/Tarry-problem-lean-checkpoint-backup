import PaperILean.UniformPlanarCellCover
import PaperILean.PlanarIntervalGraphFormat

/-! I1261: the actual local frontier of the manuscript's open set has a finite
point/coordinate-graph cover whose count and image format depend only on the
original set format. Compactness supplies bounds; openness is already a
manuscript hypothesis and supplies empty interior. -/
noncomputable section
namespace PaperI
open Set

theorem localFrontier_coordinates_interior_eq_empty
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (hE : IsOpen E)
    (z : WithLp 2 (Fin 2 → ℝ)) (R : ℝ) :
    interior ((WithLp.equiv 2 (Fin 2 → ℝ)) '' (frontier E ∩ Metric.closedBall z R)) = ∅ := by
  rw [planarLocalFrontier_coordinates]
  have hopen : IsOpen ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) :=
    planarCoordinatesHomeomorph.isOpenMap E hE
  have hf : interior (frontier ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E)) = ∅ := by
    simpa only [frontier_compl] using interior_frontier hopen.isClosed_compl
  apply subset_empty_iff.mp
  exact hf ▸ interior_mono (fun _ hx => hx.1)

theorem localFrontier_coordinates_bounded
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (z : WithLp 2 (Fin 2 → ℝ)) (R : ℝ) :
    (∀ i : Fin 2, BddBelow ((fun x => x i) ''
      ((WithLp.equiv 2 (Fin 2 → ℝ)) '' (frontier E ∩ Metric.closedBall z R)))) ∧
    (∀ i : Fin 2, BddAbove ((fun x => x i) ''
      ((WithLp.equiv 2 (Fin 2 → ℝ)) '' (frontier E ∩ Metric.closedBall z R)))) := by
  have hc := (localFrontier_isCompact E z R).image planarCoordinatesHomeomorph.continuous
  exact ⟨fun i => (hc.image (continuous_apply i)).bddBelow,
    fun i => (hc.image (continuous_apply i)).bddAbove⟩

/-- Uniformity includes the center and every real radius. Negative radii and
radius zero require no special positive-radius assumption. -/
theorem published_uniform_localFrontier_cell_cover
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    (s D : ℕ) :
    ∃ M sOut dOut : ℕ, ∀ (E : Set (WithLp 2 (Fin 2 → ℝ)))
      (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) → IsOpen E →
      ∀ (z : WithLp 2 (Fin 2 → ℝ)) (R : ℝ),
      ∃ (n : ℕ) (C : Fin n → Set (Fin 2 → ℝ)), n ≤ M ∧
        (⋃ j, C j) = (WithLp.equiv 2 (Fin 2 → ℝ)) '' (frontier E ∩ Metric.closedBall z R) ∧
        (∀ j, C j = ∅ ∨ (∃ x, C j = {x}) ∨ IsPlanarIntervalGraph (C j)) ∧
        ∀ j, ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
          (∀ q ∈ B, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined B (C j) := by
  obtain ⟨sf,df,hf⟩ := published_uniform_localFrontier_format hQE s D
  obtain ⟨M,sp,dp,hc⟩ := published_bounded_sign_format_planar_cell_cover hCAD hQE sf df
  refine ⟨M,sp,dp,?_⟩
  intro E A hAc hAd hA hE z R
  obtain ⟨B,hBc,hBd,hB⟩ := hf E A hAc hAd hA z R
  obtain ⟨hlo,hhi⟩ := localFrontier_coordinates_bounded E z R
  exact hc B _ hBc hBd hB (localFrontier_coordinates_interior_eq_empty hE z R) hlo hhi

end PaperI
