import PaperILean.SignedPlanarStripArea
import Mathlib.Topology.Connected.LocallyConnected

/-! I1259/I1263. These are the actual enlarged distance band and its
topological components, not arbitrary sets satisfying a buffer predicate.
No quantitative semialgebraic-format or counting assertion is hidden here. -/

noncomputable section
namespace PaperI
open Set MeasureTheory

def bufferedDistanceBand {X : Type*} [PseudoMetricSpace X]
    (E : Set X) (W : ℝ) : Set X :=
  {x | W/2 < Metric.infDist x Eᶜ ∧ Metric.infDist x Eᶜ < 4*W}

def bufferedBandComponent {X : Type*} [PseudoMetricSpace X]
    (E : Set X) (W : ℝ) (z : X) : Set X :=
  connectedComponentIn (bufferedDistanceBand E W) z

def bufferedComponentScale {X : Type*} [PseudoMetricSpace X]
    (E : Set X) (W : ℝ) (z : X) : ℝ :=
  max W (Metric.diam (bufferedBandComponent E W z))

theorem bufferedDistanceBand_isOpen {X : Type*} [PseudoMetricSpace X]
    (E : Set X) (W : ℝ) : IsOpen (bufferedDistanceBand E W) := by
  exact (isOpen_lt continuous_const (Metric.continuous_infDist_pt _)).inter
    (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const)

theorem bufferedDistanceBand_eq_empty_of_nonpos {X : Type*} [PseudoMetricSpace X]
    (E : Set X) {W : ℝ} (hW : W ≤ 0) : bufferedDistanceBand E W = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  have h := Metric.infDist_nonneg (x := x) (s := Eᶜ)
  have hx' := hx.2
  linarith

theorem bufferedDistanceBand_empty {X : Type*} [PseudoMetricSpace X]
    {W : ℝ} (hW : 0 < W) : bufferedDistanceBand (∅ : Set X) W = ∅ := by
  ext x
  simp [bufferedDistanceBand, Metric.infDist_zero_of_mem, hW]
  linarith

theorem bufferedDistanceBand_univ {X : Type*} [PseudoMetricSpace X]
    {W : ℝ} (hW : 0 < W) : bufferedDistanceBand (univ : Set X) W = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  have hx' : W/2 < 0 := by
    simpa only [compl_univ, Metric.infDist_empty] using hx.1
  linarith

theorem label_mem_bufferedDistanceBand {X : Type*} [PseudoMetricSpace X]
    {E : Set X} {W : ℝ} (hW : 0 < W) {z : X}
    (hz : W ≤ Metric.infDist z Eᶜ ∧ Metric.infDist z Eᶜ < 2*W) :
    z ∈ bufferedDistanceBand E W := by
  constructor <;> linarith [hz.1, hz.2]

theorem bufferedDistanceBand_subset {X : Type*} [PseudoMetricSpace X]
    (E : Set X) {W : ℝ} (hW : 0 ≤ W) : bufferedDistanceBand E W ⊆ E := by
  intro x hx
  apply Metric.ball_infDist_compl_subset (s := E)
  rw [Metric.mem_ball, dist_self]
  exact lt_of_le_of_lt (by positivity : 0 ≤ W/2) hx.1

theorem bufferedBandComponent_subset_band {X : Type*} [PseudoMetricSpace X]
    (E : Set X) (W : ℝ) (z : X) :
    bufferedBandComponent E W z ⊆ bufferedDistanceBand E W :=
  connectedComponentIn_subset _ _

theorem bufferedBandComponent_isPreconnected {X : Type*} [PseudoMetricSpace X]
    (E : Set X) (W : ℝ) (z : X) : IsPreconnected (bufferedBandComponent E W z) :=
  isPreconnected_connectedComponentIn

theorem bufferedBandComponent_isOpen {X : Type*} [PseudoMetricSpace X]
    [LocallyConnectedSpace X] (E : Set X) (W : ℝ) (z : X) :
    IsOpen (bufferedBandComponent E W z) :=
  (bufferedDistanceBand_isOpen E W).connectedComponentIn

theorem mem_bufferedBandComponent {X : Type*} [PseudoMetricSpace X]
    {E : Set X} {W : ℝ} {z : X} (hz : z ∈ bufferedDistanceBand E W) :
    z ∈ bufferedBandComponent E W z := mem_connectedComponentIn hz

theorem bufferedBandComponent_isBounded {X : Type*} [PseudoMetricSpace X]
    {E : Set X} (hE : Bornology.IsBounded E) {W : ℝ} (hW : 0 ≤ W) (z : X) :
    Bornology.IsBounded (bufferedBandComponent E W z) :=
  hE.subset ((bufferedBandComponent_subset_band E W z).trans
    (bufferedDistanceBand_subset E hW))

theorem bufferedBandComponent_buffer {X : Type*} [PseudoMetricSpace X]
    {E : Set X} {W : ℝ} {z x : X} (hx : x ∈ bufferedBandComponent E W z) :
    W/2 < Metric.infDist x Eᶜ ∧ Metric.infDist x Eᶜ < 4*W :=
  bufferedBandComponent_subset_band E W z hx

theorem exists_separated_pair_of_diam_pos {X : Type*} [PseudoMetricSpace X]
    {C : Set X} (hC : Bornology.IsBounded C) (hpos : 0 < Metric.diam C) :
    ∃ a ∈ C, ∃ b ∈ C, a ≠ b ∧ Metric.diam C/2 < dist a b ∧ dist a b ≤ Metric.diam C := by
  have hex : ∃ a ∈ C, ∃ b ∈ C, Metric.diam C/2 < dist a b := by
    by_contra! hn
    have hd := Metric.diam_le_of_forall_dist_le (by positivity : 0 ≤ Metric.diam C/2) hn
    linarith
  obtain ⟨a,ha,b,hb,hab⟩ := hex
  refine ⟨a,ha,b,hb,?_,hab,Metric.dist_le_diam_of_mem hC ha hb⟩
  intro heq
  subst b
  rw [dist_self] at hab
  linarith

theorem bufferedBandComponent_large_endpoints {X : Type*} [PseudoMetricSpace X]
    {E : Set X} (hE : Bornology.IsBounded E) {W : ℝ} (hW : 0 < W) (z : X)
    (hlarge : W < Metric.diam (bufferedBandComponent E W z)) :
    ∃ a ∈ bufferedBandComponent E W z, ∃ b ∈ bufferedBandComponent E W z,
      a ≠ b ∧ bufferedComponentScale E W z/2 < dist a b ∧
      dist a b ≤ bufferedComponentScale E W z := by
  rw [bufferedComponentScale, max_eq_right (le_of_lt hlarge)]
  exact exists_separated_pair_of_diam_pos (bufferedBandComponent_isBounded hE hW.le z)
    (hW.trans hlarge)

theorem bufferedBandComponent_subset_closedBall {X : Type*} [PseudoMetricSpace X]
    {E : Set X} (hE : Bornology.IsBounded E) {W : ℝ} (hW : 0 ≤ W)
    {z a : X} (ha : a ∈ bufferedBandComponent E W z) :
    bufferedBandComponent E W z ⊆ Metric.closedBall a (bufferedComponentScale E W z) := by
  intro x hx
  exact (Metric.dist_le_diam_of_mem (bufferedBandComponent_isBounded hE hW z) hx ha).trans
    (le_max_right _ _)

end PaperI
