import PaperILean.OriginalArclengthTube
import PaperILean.UniformClosedLocalFrontierCover

/-! I1261: sum the original arclength/square estimates over the actual
uniformly bounded local-frontier arc/point cover. The final constant precedes
all coefficients, E, centers, radii and widths. Component localization and
delta-grid packing are separate, still required applications. -/

noncomputable section
namespace PaperI
open Set Metric MeasureTheory

theorem closed_monotone_planar_cell_isCompact (S : Set (Fin 2 → ℝ))
    (hS : S = ∅ ∨ (∃ x, S = {x}) ∨ IsClosedPlanarMonotoneArc S) :
    IsCompact ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' S) := by
  rcases hS with rfl | ⟨x,rfl⟩ | ⟨i,a,b,γ,hab,hc,_,hm,rfl⟩
  · simpa only [image_empty] using isCompact_empty
  · simpa only [image_singleton] using isCompact_singleton
  · simpa only [image_image,planarArcImage,Function.comp_def] using isCompact_planarArcImage hc

theorem original_square_planar_cell_ctube_area (S : Set (Fin 2 → ℝ))
    (hS : S = ∅ ∨ (∃ x, S = {x}) ∨ IsClosedPlanarMonotoneArc S)
    {W R : ℝ} (hW : 0 < W) (hWR : W ≤ R) (z : EuclideanSpace ℝ (Fin 2))
    (hball : (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' S ⊆ closedBall z R) :
    volume (cthickening (4*W) ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' S)) ≤
      ENNReal.ofReal (500*R*W) := by
  rcases hS with rfl | ⟨p,rfl⟩ | ⟨i,a,b,γ,hab,hc,_,hm,rfl⟩
  · simp only [image_empty,cthickening_empty,measure_empty,zero_le]
  · have he : (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' {p} =
        planarArcImage (fun _ => p) 0 0 := by
      rw [image_singleton,planarArcImage_const p le_rfl]
    rw [he] at hball ⊢
    exact original_square_four_width_ctube_area_linear le_rfl hW hWR continuousOn_const
      (fun _ => Or.inl monotoneOn_const) z hball
  · have he : (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' (γ '' Icc a b) =
        planarArcImage γ a b := by rw [image_image]; rfl
    rw [he] at hball ⊢
    exact original_square_four_width_ctube_area_linear hab.le hW hWR hc hm z hball

theorem original_square_finite_planar_cell_ctube_area {n : ℕ}
    (C : Fin n → Set (Fin 2 → ℝ))
    (hC : ∀ j, C j = ∅ ∨ (∃ x, C j = {x}) ∨ IsClosedPlanarMonotoneArc (C j))
    {W R : ℝ} (hW : 0 < W) (hWR : W ≤ R) (z : EuclideanSpace ℝ (Fin 2))
    (hball : ∀ j, (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' C j ⊆ closedBall z R) :
    volume (cthickening (4*W) (⋃ j, (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' C j)) ≤
      ENNReal.ofReal ((n : ℝ)*500*R*W) := by
  simpa only [Fintype.card_fin,mul_assoc] using finite_union_planar_ctube_area
    (fun j => (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' C j)
    (fun j => closed_monotone_planar_cell_isCompact (C j) (hC j))
    (4*W) (500*R*W) (by positivity)
    (fun j => original_square_planar_cell_ctube_area (C j) (hC j) hW hWR z (hball j))

theorem published_uniform_original_localFrontier_tube_area
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hMono : PublishedOneVariableMonotonicity)
    (s D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Set (WithLp 2 (Fin 2 → ℝ)))
      (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) → IsOpen E →
      ∀ (z : WithLp 2 (Fin 2 → ℝ)) (R W : ℝ), 0 < W → W ≤ R →
      volume (cthickening (4*W) (frontier E ∩ closedBall z R)) ≤ ENNReal.ofReal (K*R*W) ∧
      volume (thickening (4*W) (frontier E ∩ closedBall z R)) ≤ ENNReal.ofReal (K*R*W) := by
  obtain ⟨M,sp,dp,hcover⟩ := published_uniform_closed_localFrontier_cover hCAD hCell hHardt hQE hMono s D
  refine ⟨((M : ℝ)+1)*500,by positivity,?_⟩
  intro E A hAc hAd hA hE z R W hW hWR
  obtain ⟨n,C,hn,hu,hcases,_⟩ := hcover E A hAc hAd hA hE z R
  have hunion : (⋃ j, (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' C j) = frontier E ∩ closedBall z R := by
    rw [← image_iUnion,hu,Equiv.symm_image_image]
  have hball (j : Fin n) : (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' C j ⊆ closedBall z R := by
    intro x hx
    have hx' : x ∈ ⋃ j, (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' C j := mem_iUnion.mpr ⟨j,hx⟩
    rw [hunion] at hx'
    exact hx'.2
  have hbound := original_square_finite_planar_cell_ctube_area C hcases hW hWR z hball
  rw [hunion] at hbound
  have hfinal : volume (cthickening (4*W) (frontier E ∩ closedBall z R)) ≤
      ENNReal.ofReal (((M : ℝ)+1)*500*R*W) := by
    refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    have hn' : (n : ℝ) ≤ M+1 := by exact_mod_cast hn.trans (Nat.le_succ M)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hn' (by norm_num)) (hW.le.trans hWR)) hW.le
  exact ⟨hfinal,(measure_mono (thickening_subset_cthickening _ _)).trans hfinal⟩

end PaperI
