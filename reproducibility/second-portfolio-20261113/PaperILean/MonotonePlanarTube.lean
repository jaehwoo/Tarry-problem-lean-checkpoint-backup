import PaperILean.MonotonePlanarArcVariation
import PaperILean.PlanarTubeMeshArea

/-! I1261: the local coordinate-monotone arc estimate, with absolute constants
chosen independently of the arc and all parameters. This does not construct
the uniformly bounded semialgebraic decomposition of the actual boundary.
Closed tubes are bounded first; open tubes follow by inclusion. -/

noncomputable section
namespace PaperI
open Set Metric MeasureTheory
open scoped BigOperators ENNReal

def planarArcImage (γ : ℝ → Fin 2 → ℝ) (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  (fun t => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t)) '' Icc a b

theorem isCompact_planarArcImage {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hc : ContinuousOn γ (Icc a b)) : IsCompact (planarArcImage γ a b) :=
  isCompact_Icc.image_of_continuousOn ((PiLp.continuous_equiv_symm 2 _).comp_continuousOn hc)

/-- Isolated boundary points can be included as constant arcs, without a
nondegeneracy assumption on the curve or on its parameter interval. -/
theorem planarArcImage_const (p : Fin 2 → ℝ) {a b : ℝ} (hab : a ≤ b) :
    planarArcImage (fun _ => p) a b = {(WithLp.equiv 2 (Fin 2 → ℝ)).symm p} := by
  ext x
  constructor
  · rintro ⟨t,_,rfl⟩
    rfl
  · intro hx
    exact ⟨a,⟨le_rfl,hab⟩,(mem_singleton_iff.mp hx).symm⟩

theorem planar_arc_tubes_measurable (γ : ℝ → Fin 2 → ℝ) (a b W : ℝ) :
    MeasurableSet (thickening W (planarArcImage γ a b)) ∧
      MeasurableSet (cthickening W (planarArcImage γ a b)) :=
  ⟨isOpen_thickening.measurableSet,isClosed_cthickening.measurableSet⟩

theorem monotone_planar_arc_ctube_area_variation {γ : ℝ → Fin 2 → ℝ} {a b W : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b)) :
    volume (cthickening W (planarArcImage γ a b)) ≤
      ENNReal.ofReal (4*Real.pi*((|γ b 0-γ a 0|+|γ b 1-γ a 1|)*W+W^2)) := by
  obtain ⟨n,_,times,_,hcount,hmesh⟩ := monotone_planar_arc_finite_mesh hab hW hc hm
  have hcover : ∀ y ∈ planarArcImage γ a b, ∃ i,
      dist y ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ (times i))) < W := by
    rintro y ⟨t,ht,rfl⟩
    exact hmesh t ht
  refine (finite_mesh_planar_ctube_area _ (isCompact_planarArcImage hc) n _ W hW.le hcover).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcount hW.le)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) Real.pi_pos.le)
  nlinarith

/-- The W² term is retained here; W need not be smaller than R. -/
theorem monotone_planar_arc_ctube_area_radius {γ : ℝ → Fin 2 → ℝ} {a b W R : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b))
    (z : EuclideanSpace ℝ (Fin 2)) (hball : planarArcImage γ a b ⊆ closedBall z R) :
    volume (cthickening W (planarArcImage γ a b)) ≤
      ENNReal.ofReal (16*Real.pi*R*W+4*Real.pi*W^2) := by
  have hV := planar_endpoint_coordinate_variation_le_four_radius γ a b z R
    (hball ⟨a,⟨le_rfl,hab⟩,rfl⟩) (hball ⟨b,⟨hab,le_rfl⟩,rfl⟩)
  refine (monotone_planar_arc_ctube_area_variation hab hW hc hm).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hV hW.le)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) Real.pi_pos.le)
  nlinarith

theorem monotone_planar_arc_ctube_area_linear {γ : ℝ → Fin 2 → ℝ} {a b W R : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hWR : W ≤ R) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b))
    (z : EuclideanSpace ℝ (Fin 2)) (hball : planarArcImage γ a b ⊆ closedBall z R) :
    volume (cthickening W (planarArcImage γ a b)) ≤ ENNReal.ofReal (20*Real.pi*R*W) := by
  refine (monotone_planar_arc_ctube_area_radius hab hW hc hm z hball).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hWR hW.le)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) Real.pi_pos.le)
  nlinarith

theorem monotone_planar_arc_tube_area_linear {γ : ℝ → Fin 2 → ℝ} {a b W R : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hWR : W ≤ R) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b))
    (z : EuclideanSpace ℝ (Fin 2)) (hball : planarArcImage γ a b ⊆ closedBall z R) :
    volume (thickening W (planarArcImage γ a b)) ≤ ENNReal.ofReal (20*Real.pi*R*W) :=
  (measure_mono (thickening_subset_cthickening W _)).trans
    (monotone_planar_arc_ctube_area_linear hab hW hWR hc hm z hball)

/-- C is chosen before the radius, width, center, interval and curve. -/
theorem monotone_planar_arc_uniform_tube_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (R W : ℝ) (z : EuclideanSpace ℝ (Fin 2))
      (γ : ℝ → Fin 2 → ℝ) (a b : ℝ),
      a ≤ b → 0 < W → W ≤ R → ContinuousOn γ (Icc a b) →
      (∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
        AntitoneOn (fun t => γ t i) (Icc a b)) →
      planarArcImage γ a b ⊆ closedBall z R →
      volume (cthickening W (planarArcImage γ a b)) ≤ ENNReal.ofReal (C*R*W) ∧
      volume (thickening W (planarArcImage γ a b)) ≤ ENNReal.ofReal (C*R*W) := by
  refine ⟨20*Real.pi,by positivity,?_⟩
  intro R W z γ a b hab hW hWR hc hm hball
  exact ⟨monotone_planar_arc_ctube_area_linear hab hW hWR hc hm z hball,
    monotone_planar_arc_tube_area_linear hab hW hWR hc hm z hball⟩

/-- The manuscript uses a 4W tube but assumes only W ≤ R, not 4W ≤ R. -/
theorem monotone_planar_arc_ctube_area_four_width {γ : ℝ → Fin 2 → ℝ} {a b W R : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hWR : W ≤ R) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b))
    (z : EuclideanSpace ℝ (Fin 2)) (hball : planarArcImage γ a b ⊆ closedBall z R) :
    volume (cthickening (4*W) (planarArcImage γ a b)) ≤
      ENNReal.ofReal (128*Real.pi*R*W) := by
  refine (monotone_planar_arc_ctube_area_radius hab (by positivity : 0 < 4*W) hc hm z hball).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hWR hW.le)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) Real.pi_pos.le)
  nlinarith

/-- Finite unions allow overlapping arcs, repeated arcs, constant arcs and no
arcs. This is a geometric implication, not a uniform boundary decomposition. -/
theorem finite_monotone_planar_arcs_four_width_tube_area {ι : Type*} [Fintype ι]
    (γ : ι → ℝ → Fin 2 → ℝ) (a b : ι → ℝ) (R W : ℝ)
    (hab : ∀ j, a j ≤ b j) (hW : 0 < W) (hWR : W ≤ R)
    (hc : ∀ j, ContinuousOn (γ j) (Icc (a j) (b j)))
    (hm : ∀ j i, MonotoneOn (fun t => γ j t i) (Icc (a j) (b j)) ∨
      AntitoneOn (fun t => γ j t i) (Icc (a j) (b j)))
    (z : EuclideanSpace ℝ (Fin 2))
    (hball : ∀ j, planarArcImage (γ j) (a j) (b j) ⊆ closedBall z R) :
    volume (cthickening (4*W) (⋃ j, planarArcImage (γ j) (a j) (b j))) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ)*128*Real.pi*R*W) := by
  simpa only [mul_assoc] using finite_union_planar_ctube_area
    (fun j => planarArcImage (γ j) (a j) (b j)) (fun j => isCompact_planarArcImage (hc j))
    (4*W) (128*Real.pi*R*W) (by positivity)
    (fun j => monotone_planar_arc_ctube_area_four_width (hab j) hW hWR (hc j) (hm j) z (hball j))

theorem finite_monotone_planar_arcs_four_width_tube_real_area {ι : Type*} [Fintype ι]
    (γ : ι → ℝ → Fin 2 → ℝ) (a b : ι → ℝ) (R W : ℝ)
    (hab : ∀ j, a j ≤ b j) (hW : 0 < W) (hWR : W ≤ R)
    (hc : ∀ j, ContinuousOn (γ j) (Icc (a j) (b j)))
    (hm : ∀ j i, MonotoneOn (fun t => γ j t i) (Icc (a j) (b j)) ∨
      AntitoneOn (fun t => γ j t i) (Icc (a j) (b j)))
    (z : EuclideanSpace ℝ (Fin 2))
    (hball : ∀ j, planarArcImage (γ j) (a j) (b j) ⊆ closedBall z R) :
    volume (cthickening (4*W) (⋃ j, planarArcImage (γ j) (a j) (b j))) ≠ ⊤ ∧
      (volume (cthickening (4*W) (⋃ j, planarArcImage (γ j) (a j) (b j)))).toReal ≤
        (Fintype.card ι : ℝ)*128*Real.pi*R*W := by
  have h := finite_monotone_planar_arcs_four_width_tube_area γ a b R W hab hW hWR hc hm z hball
  have hR : 0 ≤ R := hW.le.trans hWR
  exact ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top h,
    ENNReal.toReal_le_of_le_ofReal (by positivity) h⟩

end PaperI
