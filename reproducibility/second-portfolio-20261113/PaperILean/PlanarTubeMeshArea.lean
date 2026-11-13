import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic

/-! I1261: explicit Euclidean area from a finite mesh. Balls of radius 2W
replace the manuscript's square cover, with an explicit absolute constant.
Only finite subadditivity is used: centers and tubes may coincide or overlap. -/

noncomputable section
namespace PaperI
open Set Metric MeasureTheory
open scoped BigOperators ENNReal

theorem finite_mesh_thickening_subset_balls {X : Type*} [PseudoMetricSpace X]
    (S : Set X) (n : ℕ) (p : Fin n → X) (W : ℝ)
    (hmesh : ∀ y ∈ S, ∃ i, dist y (p i) < W) :
    thickening W S ⊆ ⋃ i, ball (p i) (2*W) := by
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_thickening_iff.mp hx
  obtain ⟨i,hi⟩ := hmesh y hy
  exact mem_iUnion.mpr ⟨i,(dist_triangle x y (p i)).trans_lt (by linarith)⟩

theorem planar_finite_ball_union_area (n : ℕ) (p : Fin n → EuclideanSpace ℝ (Fin 2))
    (W : ℝ) (hW : 0 ≤ W) :
    volume (⋃ i, ball (p i) (2*W)) ≤ ENNReal.ofReal (4*Real.pi*(n : ℝ)*W^2) := by
  calc
    volume (⋃ i, ball (p i) (2*W)) ≤ ∑ i, volume (ball (p i) (2*W)) :=
      measure_iUnion_fintype_le volume _
    _ = (n : ℝ≥0∞)*(ENNReal.ofReal (2*W)^2*ENNReal.ofReal Real.pi) := by simp
    _ = ENNReal.ofReal (4*Real.pi*(n : ℝ)*W^2) := by
      rw [show 4*Real.pi*(n : ℝ)*W^2=(n : ℝ)*((2*W)^2*Real.pi) by ring,
        ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_pow (by positivity)]

theorem finite_mesh_planar_tube_area (S : Set (EuclideanSpace ℝ (Fin 2)))
    (n : ℕ) (p : Fin n → EuclideanSpace ℝ (Fin 2)) (W : ℝ) (hW : 0 ≤ W)
    (hmesh : ∀ y ∈ S, ∃ i, dist y (p i) < W) :
    volume (thickening W S) ≤ ENNReal.ofReal (4*Real.pi*(n : ℝ)*W^2) :=
  (measure_mono (finite_mesh_thickening_subset_balls S n p W hmesh)).trans
    (planar_finite_ball_union_area n p W hW)

theorem finite_mesh_cthickening_subset_balls {X : Type*} [PseudoMetricSpace X]
    (S : Set X) (hS : IsCompact S) (n : ℕ) (p : Fin n → X) (W : ℝ) (hW : 0 ≤ W)
    (hmesh : ∀ y ∈ S, ∃ i, dist y (p i) < W) :
    cthickening W S ⊆ ⋃ i, ball (p i) (2*W) := by
  rw [hS.cthickening_eq_biUnion_closedBall hW]
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp hx
  obtain ⟨i,hi⟩ := hmesh y hy
  have hxy' : dist x y ≤ W := hxy
  exact mem_iUnion.mpr ⟨i,(dist_triangle x y (p i)).trans_lt (by linarith)⟩

theorem finite_mesh_planar_ctube_area (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : IsCompact S) (n : ℕ) (p : Fin n → EuclideanSpace ℝ (Fin 2))
    (W : ℝ) (hW : 0 ≤ W) (hmesh : ∀ y ∈ S, ∃ i, dist y (p i) < W) :
    volume (cthickening W S) ≤ ENNReal.ofReal (4*Real.pi*(n : ℝ)*W^2) :=
  (measure_mono (finite_mesh_cthickening_subset_balls S hS n p W hW hmesh)).trans
    (planar_finite_ball_union_area n p W hW)

theorem finite_union_planar_tube_area {ι : Type*} [Fintype ι]
    (S : ι → Set (EuclideanSpace ℝ (Fin 2))) (W A : ℝ)
    (harea : ∀ i, volume (thickening W (S i)) ≤ ENNReal.ofReal A) :
    volume (thickening W (⋃ i, S i)) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ)*A) := by
  rw [thickening_iUnion]
  calc
    volume (⋃ i, thickening W (S i)) ≤ ∑ i, volume (thickening W (S i)) :=
      measure_iUnion_fintype_le volume _
    _ ≤ ∑ _i : ι, ENNReal.ofReal A := Finset.sum_le_sum (fun i _ => harea i)
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ)*A) := by
      simp [ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card ι))]

theorem finite_union_planar_ctube_area {ι : Type*} [Fintype ι]
    (S : ι → Set (EuclideanSpace ℝ (Fin 2))) (hS : ∀ i, IsCompact (S i))
    (W A : ℝ) (hW : 0 ≤ W)
    (harea : ∀ i, volume (cthickening W (S i)) ≤ ENNReal.ofReal A) :
    volume (cthickening W (⋃ i, S i)) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ)*A) := by
  have hsub : cthickening W (⋃ i, S i) ⊆ ⋃ i, cthickening W (S i) := by
    rw [(isCompact_iUnion hS).cthickening_eq_biUnion_closedBall hW]
    intro x hx
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨i,closedBall_subset_cthickening hi W hxy⟩
  calc
    volume (cthickening W (⋃ i, S i)) ≤ volume (⋃ i, cthickening W (S i)) := measure_mono hsub
    _ ≤ ∑ i, volume (cthickening W (S i)) := measure_iUnion_fintype_le volume _
    _ ≤ ∑ _i : ι, ENNReal.ofReal A := Finset.sum_le_sum (fun i _ => harea i)
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ)*A) := by
      simp [ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card ι))]

end PaperI
