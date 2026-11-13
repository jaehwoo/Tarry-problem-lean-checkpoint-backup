import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-! I1265: the actual displacement image of a set of endpoints relative to
an anchor. The enclosing ball is a proved upper bound, not the definition.
The family bound uses one common ball even for arbitrary parameter unions. -/

noncomputable section
namespace PaperI
open Set Metric MeasureTheory

def relativePlanarEndpoints (a : EuclideanSpace ℝ (Fin 2))
    (S : Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) :=
  (fun x => x-a) '' S

theorem relativePlanarEndpoints_empty (a : EuclideanSpace ℝ (Fin 2)) :
    relativePlanarEndpoints a ∅ = ∅ := by
  simp [relativePlanarEndpoints]

theorem relativePlanarEndpoints_union (a : EuclideanSpace ℝ (Fin 2))
    (S T : Set (EuclideanSpace ℝ (Fin 2))) :
    relativePlanarEndpoints a (S ∪ T) =
      relativePlanarEndpoints a S ∪ relativePlanarEndpoints a T := by
  exact image_union _ _ _

theorem relativePlanarEndpoints_translation (a v : EuclideanSpace ℝ (Fin 2))
    (S : Set (EuclideanSpace ℝ (Fin 2))) :
    relativePlanarEndpoints (a+v) ((fun x => x+v) '' S) =
      relativePlanarEndpoints a S := by
  simp only [relativePlanarEndpoints,← image_comp,Function.comp_def,add_sub_add_right_eq_sub]

theorem relativePlanarEndpoints_subset_closedBall_iff
    (a : EuclideanSpace ℝ (Fin 2)) (S : Set (EuclideanSpace ℝ (Fin 2))) (R : ℝ) :
    relativePlanarEndpoints a S ⊆ closedBall 0 R ↔ S ⊆ closedBall a R := by
  constructor
  · intro h x hx
    simpa only [mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero] using h ⟨x,hx,rfl⟩
  · rintro h x ⟨y,hy,rfl⟩
    simpa only [mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero] using h hy

theorem planar_closedBall_double_scale_volume (a : EuclideanSpace ℝ (Fin 2))
    {L : ℝ} (hL : 0 ≤ L) :
    volume (closedBall a (2*L)) = ENNReal.ofReal (4*Real.pi*L^2) := by
  rw [EuclideanSpace.volume_closedBall_fin_two,
    show 4*Real.pi*L^2=(2*L)^2*Real.pi by ring,
    ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_pow (by positivity)]

theorem planar_area_of_subset_double_scale_ball
    {S : Set (EuclideanSpace ℝ (Fin 2))} {a : EuclideanSpace ℝ (Fin 2)}
    {L : ℝ} (hL : 0 ≤ L) (hS : S ⊆ closedBall a (2*L)) :
    volume S ≤ ENNReal.ofReal (4*Real.pi*L^2) := by
  exact (measure_mono hS).trans_eq (planar_closedBall_double_scale_volume a hL)

theorem planar_relative_endpoints_area
    {S : Set (EuclideanSpace ℝ (Fin 2))} {a : EuclideanSpace ℝ (Fin 2)}
    {L : ℝ} (hL : 0 ≤ L) (hS : S ⊆ closedBall a (2*L)) :
    volume (relativePlanarEndpoints a S) ≤ ENNReal.ofReal (4*Real.pi*L^2) := by
  exact planar_area_of_subset_double_scale_ball hL
    ((relativePlanarEndpoints_subset_closedBall_iff a S (2*L)).mpr hS)

theorem planar_finite_real_area_of_outer_bound
    {S : Set (EuclideanSpace ℝ (Fin 2))} {A : ℝ} (hA : 0 ≤ A)
    (hS : volume S ≤ ENNReal.ofReal A) :
    volume S ≠ ⊤ ∧ volume.real S ≤ A := by
  refine ⟨ne_of_lt (hS.trans_lt ENNReal.ofReal_lt_top),?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hS).trans_eq (ENNReal.toReal_ofReal hA)

theorem planar_relative_endpoint_family_area {ι : Type*}
    (a : ι → EuclideanSpace ℝ (Fin 2)) (S : ι → Set (EuclideanSpace ℝ (Fin 2)))
    {L : ℝ} (hL : 0 ≤ L) (hS : ∀ i, S i ⊆ closedBall (a i) (2*L)) :
    volume (⋃ i, relativePlanarEndpoints (a i) (S i)) ≤ ENNReal.ofReal (4*Real.pi*L^2) ∧
      volume (⋃ i, relativePlanarEndpoints (a i) (S i)) ≠ ⊤ ∧
      volume.real (⋃ i, relativePlanarEndpoints (a i) (S i)) ≤ 4*Real.pi*L^2 := by
  have hsub : (⋃ i, relativePlanarEndpoints (a i) (S i)) ⊆ closedBall 0 (2*L) := by
    refine iUnion_subset ?_
    intro i
    exact (relativePlanarEndpoints_subset_closedBall_iff _ _ _).mpr (hS i)
  have harea := planar_area_of_subset_double_scale_ball hL hsub
  exact ⟨harea,planar_finite_real_area_of_outer_bound (by positivity) harea⟩

end PaperI
