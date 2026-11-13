import PaperILean.PlanarSquaredDistanceBand
import Mathlib.Topology.MetricSpace.Thickening

/-! I1261: localize the actual distance-band component and every nonnegative
local-width enlargement to a tube of the actual local frontier. Components
need not be closed; closed-thickening composition includes their closure. -/

noncomputable section
namespace PaperI
open Set Metric

theorem bufferedComponentScale_pos {X : Type*} [PseudoMetricSpace X]
    (E : Set X) {W : ℝ} (hW : 0 < W) (z : X) :
    0 < bufferedComponentScale E W z :=
  hW.trans_le (le_max_left _ _)

theorem bufferedBandComponent_mem_near_localFrontier
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hb : Bornology.IsBounded E)
    {W : ℝ} (hW : 0 < W) {z a x : EuclideanSpace ℝ (Fin 2)}
    (ha : a ∈ bufferedBandComponent E W z) (hx : x ∈ bufferedBandComponent E W z) :
    ∃ y ∈ frontier E ∩ closedBall a (5*bufferedComponentScale E W z),
      dist x y = infDist x Eᶜ ∧ dist x y < 4*W := by
  have hxE := bufferedDistanceBand_subset E hW.le
    (bufferedBandComponent_subset_band E W z hx)
  obtain ⟨y,hy,hxy⟩ := exists_mem_frontier_infDist_compl_eq_dist hxE
    (nonempty_compl.mp (planar_compl_nonempty_of_isBounded hb))
  have hnear : dist x y < 4*W := by
    rw [← hxy]
    exact (bufferedBandComponent_buffer hx).2
  have hxa := bufferedBandComponent_subset_closedBall hb hW.le ha hx
  have hWL : W ≤ bufferedComponentScale E W z := le_max_left _ _
  refine ⟨y,⟨hy,?_⟩,hxy.symm,hnear⟩
  change dist y a ≤ _
  calc
    dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
    _ ≤ 5*bufferedComponentScale E W z := by
      rw [dist_comm y x]
      have : dist x a ≤ bufferedComponentScale E W z := hxa
      linarith

theorem bufferedBandComponent_subset_localFrontier_thickening
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hb : Bornology.IsBounded E)
    {W : ℝ} (hW : 0 < W) {z a : EuclideanSpace ℝ (Fin 2)}
    (ha : a ∈ bufferedBandComponent E W z) :
    bufferedBandComponent E W z ⊆
      thickening (4*W) (frontier E ∩ closedBall a (5*bufferedComponentScale E W z)) := by
  intro x hx
  obtain ⟨y,hy,_,hxy⟩ := bufferedBandComponent_mem_near_localFrontier hb hW ha hx
  exact mem_thickening_iff.mpr ⟨y,hy,hxy⟩

theorem bufferedBandComponent_cthickening_subset_localFrontier
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hb : Bornology.IsBounded E)
    {W r : ℝ} (hW : 0 < W) (hr : 0 ≤ r) {z a : EuclideanSpace ℝ (Fin 2)}
    (ha : a ∈ bufferedBandComponent E W z) :
    cthickening r (bufferedBandComponent E W z) ⊆
      cthickening (r+4*W) (frontier E ∩ closedBall a (5*bufferedComponentScale E W z)) := by
  exact (cthickening_subset_of_subset r
    ((bufferedBandComponent_subset_localFrontier_thickening hb hW ha).trans
      (thickening_subset_cthickening _ _))).trans
    (cthickening_cthickening_subset hr (by positivity) _)

theorem bufferedBandComponent_scaled_enlargement_localization
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hb : Bornology.IsBounded E)
    {W b : ℝ} (hW : 0 < W) (hb0 : 0 ≤ b) {z a : EuclideanSpace ℝ (Fin 2)}
    (ha : a ∈ bufferedBandComponent E W z) :
    cthickening (b*W) (bufferedBandComponent E W z) ⊆
      cthickening ((b+4)*W)
        (frontier E ∩ closedBall a ((b+5)*bufferedComponentScale E W z)) := by
  have hball : closedBall a (5*bufferedComponentScale E W z) ⊆
      closedBall a ((b+5)*bufferedComponentScale E W z) :=
    closedBall_subset_closedBall (by
      nlinarith [bufferedComponentScale_pos E hW z])
  convert (bufferedBandComponent_cthickening_subset_localFrontier hb hW
    (mul_nonneg hb0 hW.le) ha).trans
    (cthickening_subset_of_subset _ (inter_subset_inter_right _ hball)) using 1 <;> ring

theorem bufferedBandComponent_closure_subset_localFrontier
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hb : Bornology.IsBounded E)
    {W : ℝ} (hW : 0 < W) {z a : EuclideanSpace ℝ (Fin 2)}
    (ha : a ∈ bufferedBandComponent E W z) :
    closure (bufferedBandComponent E W z) ⊆
      cthickening (4*W) (frontier E ∩ closedBall a (5*bufferedComponentScale E W z)) := by
  simpa only [cthickening_zero,zero_add] using
    bufferedBandComponent_cthickening_subset_localFrontier hb hW (r:=0) le_rfl ha

end PaperI
