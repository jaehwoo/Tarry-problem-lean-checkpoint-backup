import PaperILean.EuclideanArclengthMesh
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.Thickening

/-! I1261: actual axis-parallel squares of side W. Each arclength mesh point
uses a 10-by-10 cluster, enough for the 4W tube and one mesh step. -/

noncomputable section
namespace PaperI
open Set Metric MeasureTheory
open scoped BigOperators ENNReal

def planarSquare (c : Fin 2 → ℝ) (W : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)) ⁻¹' Icc c (fun j => c j+W)

def planarMeshSquareCorner (p : EuclideanSpace ℝ (Fin 2)) (W : ℝ)
    (k : Fin 2 → Fin 10) : Fin 2 → ℝ := fun j => p j-5*W+(k j).val*W

theorem mem_planarSquare_iff (x : EuclideanSpace ℝ (Fin 2)) (c : Fin 2 → ℝ) (W : ℝ) :
    x ∈ planarSquare c W ↔ ∀ j, c j ≤ x j ∧ x j ≤ c j+W := by
  simp only [planarSquare,mem_preimage,mem_Icc,Pi.le_def,forall_and]
  rfl

theorem measurableSet_planarSquare (c : Fin 2 → ℝ) (W : ℝ) :
    MeasurableSet (planarSquare c W) :=
  (PiLp.continuous_equiv 2 (fun _ : Fin 2 => ℝ)).measurable isClosed_Icc.measurableSet

theorem volume_planarSquare (c : Fin 2 → ℝ) {W : ℝ} (hW : 0 ≤ W) :
    volume (planarSquare c W) = ENNReal.ofReal (W^2) := by
  rw [planarSquare,(PiLp.volume_preserving_equiv (Fin 2)).measure_preimage
    isClosed_Icc.measurableSet.nullMeasurableSet]
  simp [Real.volume_Icc_pi,Fin.prod_univ_two,← pow_two,ENNReal.ofReal_pow hW]

theorem planar_ball_five_width_square_cover (p : EuclideanSpace ℝ (Fin 2))
    {W : ℝ} (hW : 0 < W) :
    ball p (5*W) ⊆ ⋃ k : Fin 2 → Fin 10, planarSquare (planarMeshSquareCorner p W k) W := by
  intro x hx
  have hxj (j : Fin 2) : |x j-p j| < 5*W :=
    (show |x j-p j| ≤ dist x p by simpa only [Real.dist_eq] using PiLp.dist_apply_le x p j).trans_lt hx
  have hnonneg (j : Fin 2) : 0 ≤ (x j-p j+5*W)/W :=
    div_nonneg (by linarith [(abs_lt.mp (hxj j)).1]) hW.le
  have hlt (j : Fin 2) : ⌊(x j-p j+5*W)/W⌋₊ < 10 := by
    apply (Nat.floor_lt (hnonneg j)).mpr
    apply (div_lt_iff₀ hW).mpr
    norm_num
    linarith [(abs_lt.mp (hxj j)).2]
  let k : Fin 2 → Fin 10 := fun j => ⟨⌊(x j-p j+5*W)/W⌋₊,hlt j⟩
  refine mem_iUnion.mpr ⟨k,(mem_planarSquare_iff _ _ _).mpr ?_⟩
  intro j
  have hlo := (le_div_iff₀ hW).mp (Nat.floor_le (hnonneg j))
  have hhi := (div_lt_iff₀ hW).mp (Nat.lt_floor_add_one ((x j-p j+5*W)/W))
  dsimp only [planarMeshSquareCorner,k]
  constructor <;> linarith

theorem planar_mesh_square_coordinate_bounds (p x : EuclideanSpace ℝ (Fin 2))
    {W : ℝ} (hW : 0 ≤ W) (k : Fin 2 → Fin 10)
    (hx : x ∈ planarSquare (planarMeshSquareCorner p W k) W) :
    ∀ j, |x j-p j| ≤ 5*W := by
  intro j
  have hj := (mem_planarSquare_iff _ _ _).mp hx j
  have hk : ((k j).val : ℝ) ≤ 9 := by exact_mod_cast Nat.le_of_lt_succ (k j).isLt
  have hk0 : (0 : ℝ) ≤ (k j).val := Nat.cast_nonneg _
  dsimp only [planarMeshSquareCorner] at hj
  rw [abs_le]
  constructor <;> nlinarith

theorem finite_mesh_four_width_ctube_square_cover (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : IsCompact S) (n : ℕ) (p : Fin n → EuclideanSpace ℝ (Fin 2))
    {W : ℝ} (hW : 0 < W) (hmesh : ∀ y ∈ S, ∃ i, dist y (p i) < W) :
    cthickening (4*W) S ⊆
      ⋃ i, ⋃ k : Fin 2 → Fin 10, planarSquare (planarMeshSquareCorner (p i) W k) W := by
  rw [hS.cthickening_eq_biUnion_closedBall (by positivity : 0 ≤ 4*W)]
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp hx
  obtain ⟨i,hi⟩ := hmesh y hy
  have hd : dist x (p i) < 5*W :=
    (dist_triangle x y (p i)).trans_lt (by have : dist x y ≤ 4*W := hxy; linarith)
  exact mem_iUnion.mpr ⟨i,planar_ball_five_width_square_cover (p i) hW hd⟩

theorem planar_finite_square_cluster_area (n : ℕ) (p : Fin n → EuclideanSpace ℝ (Fin 2))
    {W : ℝ} (hW : 0 ≤ W) :
    volume (⋃ i, ⋃ k : Fin 2 → Fin 10, planarSquare (planarMeshSquareCorner (p i) W k) W) ≤
      ENNReal.ofReal (100*(n : ℝ)*W^2) := by
  calc
    _ ≤ ∑ i, volume (⋃ k : Fin 2 → Fin 10, planarSquare (planarMeshSquareCorner (p i) W k) W) :=
      measure_iUnion_fintype_le volume _
    _ ≤ ∑ i, ∑ k : Fin 2 → Fin 10, volume (planarSquare (planarMeshSquareCorner (p i) W k) W) :=
      Finset.sum_le_sum (fun _ _ => measure_iUnion_fintype_le volume _)
    _ = ENNReal.ofReal (100*(n : ℝ)*W^2) := by
      simp only [volume_planarSquare _ hW,Finset.sum_const,Finset.card_univ,
        Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul]
      rw [show 100*(n : ℝ)*W^2 = (n : ℝ)*(100*W^2) by ring,
        ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)]
      norm_num

theorem finite_mesh_four_width_ctube_square_area (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : IsCompact S) (n : ℕ) (p : Fin n → EuclideanSpace ℝ (Fin 2))
    {W : ℝ} (hW : 0 < W) (hmesh : ∀ y ∈ S, ∃ i, dist y (p i) < W) :
    volume (cthickening (4*W) S) ≤ ENNReal.ofReal (100*(n : ℝ)*W^2) :=
  (measure_mono (finite_mesh_four_width_ctube_square_cover S hS n p hW hmesh)).trans
    (planar_finite_square_cluster_area n p hW.le)

end PaperI
