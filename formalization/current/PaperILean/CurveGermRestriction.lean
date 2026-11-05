import PaperILean.SemialgebraicPathData

/-! I654, local restriction of a supplied continuous boundary germ. The source
need not belong to the open-time cell. The ambient-set application explicitly
retains source membership. No curve-selection existence theorem, boundary
extension of a chart, or parameter-uniform germ family is assumed here.
Obstructions were tested before this module: checkpoint_111_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set

def curveInitialSegment {X : Type*} (g : ℝ → X) (r : ℝ) : ℝ → X :=
  fun t => g (r * t)

theorem initialSegment_time_mem {ε r t : ℝ} (hr : 0 ≤ r) (hrε : r < ε)
    (ht : t ∈ Icc (0 : ℝ) 1) : r * t ∈ Ico (0 : ℝ) ε := by
  exact ⟨mul_nonneg hr ht.1, (mul_le_of_le_one_right hr ht.2).trans_lt hrε⟩

theorem initialSegment_time_pos_mem {ε r t : ℝ} (hr : 0 < r) (hrε : r < ε)
    (ht : t ∈ Ioc (0 : ℝ) 1) : r * t ∈ Ioo (0 : ℝ) ε := by
  exact ⟨mul_pos hr ht.1, (mul_le_of_le_one_right hr.le ht.2).trans_lt hrε⟩

theorem curveInitialSegment_continuousOn {X : Type*} [TopologicalSpace X]
    {g : ℝ → X} {ε r : ℝ} (hg : ContinuousOn g (Ico (0 : ℝ) ε))
    (hr : 0 ≤ r) (hrε : r < ε) :
    ContinuousOn (curveInitialSegment g r) (Icc (0 : ℝ) 1) := by
  exact hg.comp (continuous_const.mul continuous_id).continuousOn
    (fun _ ht => initialSegment_time_mem hr hrε ht)

theorem curveInitialSegment_source {X : Type*} (g : ℝ → X) (r : ℝ) :
    curveInitialSegment g r 0 = g 0 := by simp [curveInitialSegment]

theorem curveInitialSegment_target {X : Type*} (g : ℝ → X) (r : ℝ) :
    curveInitialSegment g r 1 = g r := by simp [curveInitialSegment]

theorem curveInitialSegment_mapsTo_positive {X : Type*} {g : ℝ → X}
    {C : Set X} {ε r : ℝ} (hg : MapsTo g (Ioo (0 : ℝ) ε) C)
    (hr : 0 < r) (hrε : r < ε) :
    MapsTo (curveInitialSegment g r) (Ioc (0 : ℝ) 1) C := by
  exact fun _ ht => hg (initialSegment_time_pos_mem hr hrε ht)

theorem curveInitialSegment_mapsTo_insert {X : Type*} {g : ℝ → X}
    {C : Set X} {ε r : ℝ} (hg : MapsTo g (Ioo (0 : ℝ) ε) C)
    (hr : 0 < r) (hrε : r < ε) :
    MapsTo (curveInitialSegment g r) (Icc (0 : ℝ) 1) (insert (g 0) C) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst t
    simp [curveInitialSegment]
  · exact mem_insert_of_mem _ (curveInitialSegment_mapsTo_positive hg hr hrε ⟨h,ht.2⟩)

theorem curveInitialSegment_mapsTo_ambient {X : Type*} {g : ℝ → X}
    {C S : Set X} {ε r : ℝ} (hg : MapsTo g (Ioo (0 : ℝ) ε) C)
    (hr : 0 < r) (hrε : r < ε) (h0 : g 0 ∈ S) (hC : C ⊆ S) :
    MapsTo (curveInitialSegment g r) (Icc (0 : ℝ) 1) S := by
  intro t ht
  exact (insert_subset h0 hC) (curveInitialSegment_mapsTo_insert hg hr hrε ht)

theorem curveInitialSegment_half {X : Type*} [TopologicalSpace X]
    {g : ℝ → X} {C : Set X} {ε : ℝ} (hε : 0 < ε)
    (hc : ContinuousOn g (Ico (0 : ℝ) ε)) (hm : MapsTo g (Ioo (0 : ℝ) ε) C) :
    ContinuousOn (curveInitialSegment g (ε/2)) (Icc (0 : ℝ) 1) ∧
    MapsTo (curveInitialSegment g (ε/2)) (Icc (0 : ℝ) 1) (insert (g 0) C) ∧
    curveInitialSegment g (ε/2) 0 = g 0 ∧
    curveInitialSegment g (ε/2) 1 = g (ε/2) ∧ g (ε/2) ∈ C := by
  have hr : 0 < ε/2 := by positivity
  have hrε : ε/2 < ε := by linarith
  exact ⟨curveInitialSegment_continuousOn hc hr.le hrε,
    curveInitialSegment_mapsTo_insert hm hr hrε,
    curveInitialSegment_source _ _, curveInitialSegment_target _ _, hm ⟨hr,hrε⟩⟩

end PaperI
