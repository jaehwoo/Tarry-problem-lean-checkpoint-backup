import PaperILean.ArclengthSquareMultiplicity
import PaperILean.MonotonePlanarTube

/-! Original I1261 proof: actual Euclidean arclength mesh, side-W squares,
bounded multiplicity, and finite subadditivity. The older coordinate-clock
and ball-area proof is retained but is not used to prove these estimates. -/

noncomputable section
namespace PaperI
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

theorem original_arclength_square_cover {γ : ℝ → Fin 2 → ℝ} {a b W : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ k, MonotoneOn (fun t => γ t k) (Icc a b) ∨
      AntitoneOn (fun t => γ t k) (Icc a b)) :
    ∃ n : ℕ, 0 < n ∧ ∃ times : Fin n → ℝ,
      (∀ i, times i ∈ Icc a b) ∧ StrictMono times ∧
      (∀ i, planarEuclideanLength γ a (times i) = (i.val : ℝ)*W) ∧
      (n : ℝ)*W ≤ planarEuclideanLength γ a b+W ∧
      Fintype.card (Fin n × (Fin 2 → Fin 10)) = 100*n ∧
      cthickening (4*W) (planarArcImage γ a b) ⊆
        (⋃ i, ⋃ k : Fin 2 → Fin 10, planarSquare (planarMeshSquareCorner
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ (times i))) W k) W) ∧
      ∀ x : EuclideanSpace ℝ (Fin 2),
        (Finset.univ.filter (fun ik : Fin n × (Fin 2 → Fin 10) =>
          x ∈ planarSquare (planarMeshSquareCorner
            ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ (times ik.1))) W ik.2) W)).card ≤ 2100 := by
  obtain ⟨n,hn,times,ht,hmono,he,hcount,hmesh⟩ := monotone_planar_arc_arclength_mesh hab hW hc hm
  refine ⟨n,hn,times,ht,hmono,he,hcount,?_,?_,?_⟩
  · simp [Fintype.card_fun,Nat.mul_comm]
  · apply finite_mesh_four_width_ctube_square_cover _ (isCompact_planarArcImage hc) n _ hW
    rintro y ⟨t,hti,rfl⟩
    obtain ⟨i,_,hi⟩ := hmesh t hti
    exact ⟨i,hi⟩
  · exact arclength_square_cover_multiplicity hW hm times ht hmono.monotone he

theorem original_arclength_four_width_ctube_area {γ : ℝ → Fin 2 → ℝ} {a b W : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ k, MonotoneOn (fun t => γ t k) (Icc a b) ∨
      AntitoneOn (fun t => γ t k) (Icc a b)) :
    volume (cthickening (4*W) (planarArcImage γ a b)) ≤
      ENNReal.ofReal (100*(planarEuclideanLength γ a b*W+W^2)) := by
  obtain ⟨n,_,times,_,_,_,hcount,_,hcover,_⟩ := original_arclength_square_cover hab hW hc hm
  refine ((measure_mono hcover).trans (planar_finite_square_cluster_area n _ hW.le)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [mul_le_mul_of_nonneg_right hcount hW.le]

theorem original_square_four_width_ctube_area_variation {γ : ℝ → Fin 2 → ℝ} {a b W : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ k, MonotoneOn (fun t => γ t k) (Icc a b) ∨
      AntitoneOn (fun t => γ t k) (Icc a b)) :
    volume (cthickening (4*W) (planarArcImage γ a b)) ≤
      ENNReal.ofReal (100*((|γ b 0-γ a 0|+|γ b 1-γ a 1|)*W+W^2)) := by
  refine (original_arclength_four_width_ctube_area hab hW hc hm).trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [mul_le_mul_of_nonneg_right (planar_euclidean_length_le_coordinate_variation hab hm) hW.le]

theorem original_square_four_width_ctube_area_radius {γ : ℝ → Fin 2 → ℝ} {a b W R : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ k, MonotoneOn (fun t => γ t k) (Icc a b) ∨
      AntitoneOn (fun t => γ t k) (Icc a b))
    (z : EuclideanSpace ℝ (Fin 2)) (hball : planarArcImage γ a b ⊆ closedBall z R) :
    volume (cthickening (4*W) (planarArcImage γ a b)) ≤
      ENNReal.ofReal (400*R*W+100*W^2) := by
  have hV := planar_endpoint_coordinate_variation_le_four_radius γ a b z R
    (hball ⟨a,⟨le_rfl,hab⟩,rfl⟩) (hball ⟨b,⟨hab,le_rfl⟩,rfl⟩)
  refine (original_square_four_width_ctube_area_variation hab hW hc hm).trans
    (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [mul_le_mul_of_nonneg_right hV hW.le]

theorem original_square_four_width_ctube_area_linear {γ : ℝ → Fin 2 → ℝ} {a b W R : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hWR : W ≤ R) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ k, MonotoneOn (fun t => γ t k) (Icc a b) ∨
      AntitoneOn (fun t => γ t k) (Icc a b))
    (z : EuclideanSpace ℝ (Fin 2)) (hball : planarArcImage γ a b ⊆ closedBall z R) :
    volume (cthickening (4*W) (planarArcImage γ a b)) ≤ ENNReal.ofReal (500*R*W) := by
  refine (original_square_four_width_ctube_area_radius hab hW hc hm z hball).trans
    (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [mul_le_mul_of_nonneg_right hWR hW.le]

theorem original_square_four_width_tube_area_linear {γ : ℝ → Fin 2 → ℝ} {a b W R : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hWR : W ≤ R) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ k, MonotoneOn (fun t => γ t k) (Icc a b) ∨
      AntitoneOn (fun t => γ t k) (Icc a b))
    (z : EuclideanSpace ℝ (Fin 2)) (hball : planarArcImage γ a b ⊆ closedBall z R) :
    volume (thickening (4*W) (planarArcImage γ a b)) ≤ ENNReal.ofReal (500*R*W) :=
  (measure_mono (thickening_subset_cthickening _ _)).trans
    (original_square_four_width_ctube_area_linear hab hW hWR hc hm z hball)

theorem original_square_finite_arc_tube_area {ι : Type*} [Fintype ι]
    (γ : ι → ℝ → Fin 2 → ℝ) (a b : ι → ℝ) (R W : ℝ)
    (hab : ∀ j, a j ≤ b j) (hW : 0 < W) (hWR : W ≤ R)
    (hc : ∀ j, ContinuousOn (γ j) (Icc (a j) (b j)))
    (hm : ∀ j k, MonotoneOn (fun t => γ j t k) (Icc (a j) (b j)) ∨
      AntitoneOn (fun t => γ j t k) (Icc (a j) (b j)))
    (z : EuclideanSpace ℝ (Fin 2))
    (hball : ∀ j, planarArcImage (γ j) (a j) (b j) ⊆ closedBall z R) :
    volume (cthickening (4*W) (⋃ j, planarArcImage (γ j) (a j) (b j))) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ)*500*R*W) := by
  simpa only [mul_assoc] using finite_union_planar_ctube_area
    (fun j => planarArcImage (γ j) (a j) (b j)) (fun j => isCompact_planarArcImage (hc j))
    (4*W) (500*R*W) (by positivity)
    (fun j => original_square_four_width_ctube_area_linear (hab j) hW hWR (hc j) (hm j) z (hball j))

end PaperI
