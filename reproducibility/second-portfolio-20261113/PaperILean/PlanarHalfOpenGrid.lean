import PaperILean.PlanarMeshSquares

/-! I1261: a translated square grid. Half-open cells give an exact disjoint
partition; each is contained in its closed side-delta square for the stated
local-label packing assumption. All offsets and positive mesh sizes remain
arbitrary. -/

noncomputable section
namespace PaperI
open Set Metric MeasureTheory
open scoped BigOperators

def planarGridCell (o : Fin 2 → ℝ) (δ : ℝ) (k : Fin 2 → ℤ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)) ⁻¹'
    pi univ (fun j => Ico (o j+(k j : ℝ)*δ) (o j+(k j : ℝ)*δ+δ))

def planarGridIndex (o : Fin 2 → ℝ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    Fin 2 → ℤ := fun j => ⌊(x j-o j)/δ⌋

def planarGridTouched (o : Fin 2 → ℝ) (δ : ℝ) (C : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (Fin 2 → ℤ) := {k | (C ∩ planarGridCell o δ k).Nonempty}

theorem mem_planarGridCell_iff (o : Fin 2 → ℝ) (δ : ℝ) (k : Fin 2 → ℤ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ planarGridCell o δ k ↔ ∀ j, o j+(k j : ℝ)*δ ≤ x j ∧ x j < o j+(k j : ℝ)*δ+δ := by
  simp [planarGridCell,mem_pi]

theorem measurableSet_planarGridCell (o : Fin 2 → ℝ) (δ : ℝ) (k : Fin 2 → ℤ) :
    MeasurableSet (planarGridCell o δ k) :=
  (PiLp.continuous_equiv 2 (fun _ : Fin 2 => ℝ)).measurable
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ico))

theorem volume_planarGridCell (o : Fin 2 → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (k : Fin 2 → ℤ) :
    volume (planarGridCell o δ k) = ENNReal.ofReal (δ^2) := by
  rw [planarGridCell,(PiLp.volume_preserving_equiv (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).nullMeasurableSet]
  simp [Real.volume_pi_Ico,Fin.prod_univ_two,← pow_two,ENNReal.ofReal_pow hδ]

theorem planarGridCell_subset_square (o : Fin 2 → ℝ) (δ : ℝ) (k : Fin 2 → ℤ) :
    planarGridCell o δ k ⊆ planarSquare (fun j => o j+(k j : ℝ)*δ) δ := by
  intro x hx
  apply (mem_planarSquare_iff _ _ _).mpr
  intro j
  exact ⟨((mem_planarGridCell_iff _ _ _ _).mp hx j).1,
    ((mem_planarGridCell_iff _ _ _ _).mp hx j).2.le⟩

theorem mem_planarGridCell_index (o : Fin 2 → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (x : EuclideanSpace ℝ (Fin 2)) : x ∈ planarGridCell o δ (planarGridIndex o δ x) := by
  apply (mem_planarGridCell_iff _ _ _ _).mpr
  intro j
  have hlo := (le_div_iff₀ hδ).mp (Int.floor_le ((x j-o j)/δ))
  have hhi := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one ((x j-o j)/δ))
  dsimp only [planarGridIndex]
  constructor <;> linarith

theorem planarGridIndex_eq_of_mem {o : Fin 2 → ℝ} {δ : ℝ} (hδ : 0 < δ)
    {k : Fin 2 → ℤ} {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ planarGridCell o δ k) :
    planarGridIndex o δ x = k := by
  funext j
  apply Int.floor_eq_iff.mpr
  have hj := (mem_planarGridCell_iff _ _ _ _).mp hx j
  constructor
  · apply (le_div_iff₀ hδ).mpr
    linarith [hj.1]
  · apply (div_lt_iff₀ hδ).mpr
    linarith [hj.2]

theorem planarGridCell_pairwiseDisjoint (o : Fin 2 → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Pairwise (fun k l => Disjoint (planarGridCell o δ k) (planarGridCell o δ l)) := by
  intro k l hkl
  rw [disjoint_left]
  intro x hx hy
  exact hkl ((planarGridIndex_eq_of_mem hδ hx).symm.trans (planarGridIndex_eq_of_mem hδ hy))

theorem planarGridCell_dist_le {o : Fin 2 → ℝ} {δ : ℝ} {k : Fin 2 → ℤ}
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ planarGridCell o δ k)
    (hy : y ∈ planarGridCell o δ k) : dist x y ≤ 2*δ := by
  have hj (j : Fin 2) : |x j-y j| ≤ δ := by
    have hxj := (mem_planarGridCell_iff _ _ _ _).mp hx j
    have hyj := (mem_planarGridCell_iff _ _ _ _).mp hy j
    rw [abs_le]
    constructor <;> linarith [hxj.1,hxj.2,hyj.1,hyj.2]
  have hd := planar_euclidean_dist_le_coordinate_sum
    ((WithLp.equiv 2 (Fin 2 → ℝ)) x) ((WithLp.equiv 2 (Fin 2 → ℝ)) y)
  simp only [Equiv.symm_apply_apply,WithLp.equiv_pi_apply] at hd
  linarith [hj 0,hj 1]

theorem touched_planarGridCell_subset_cthickening {o : Fin 2 → ℝ} {δ : ℝ}
    {C : Set (EuclideanSpace ℝ (Fin 2))} {k : Fin 2 → ℤ}
    (hk : k ∈ planarGridTouched o δ C) : planarGridCell o δ k ⊆ cthickening (2*δ) C := by
  obtain ⟨y,hyC,hy⟩ := hk
  intro x hx
  exact closedBall_subset_cthickening hyC (2*δ) (planarGridCell_dist_le hx hy)

theorem planarGridTouched_cover (o : Fin 2 → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (C : Set (EuclideanSpace ℝ (Fin 2))) :
    C ⊆ ⋃ k ∈ planarGridTouched o δ C, planarGridCell o δ k := by
  intro x hx
  have hg := mem_planarGridCell_index o hδ x
  exact mem_iUnion₂.mpr ⟨planarGridIndex o δ x,⟨x,hx,hg⟩,hg⟩

end PaperI
