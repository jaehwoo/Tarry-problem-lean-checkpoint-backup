import PaperILean.PlanarSquaredDistanceBand

/-! Original I1259: a uniform bounded search region for the closed-complement
minimum. Coordinates use the Euclidean WithLp 2 metric, not the sup metric. -/

noncomputable section
namespace PaperI
open Set

def planarCoordinateBox (T : ℝ) : Set (Fin 2 → ℝ) :=
  {x | ∀ j, |x j| ≤ T}

theorem planarCoordinateBox_mono {T U : ℝ} (h : T ≤ U) :
    planarCoordinateBox T ⊆ planarCoordinateBox U :=
  fun _ hx j => (hx j).trans h

theorem planarCoordinateBox_zero : planarCoordinateBox 0 = {0} := by
  ext x
  simp only [planarCoordinateBox, mem_setOf_eq, abs_nonpos_iff, mem_singleton_iff]
  exact ⟨fun h => funext h, fun h j => congrFun h j⟩

theorem planar_bounded_search_witness {T : ℝ} (hT : 0 ≤ T)
    {E : Set (WithLp 2 (Fin 2 → ℝ))}
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    {x : Fin 2 → ℝ} (hx : x ∈ planarCoordinateBox T) :
    ∃ y : Fin 2 → ℝ,
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm y ∉ E ∧
      dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x)
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm y) ≤ 3*T+1 := by
  let e := WithLp.equiv 2 (Fin 2 → ℝ)
  let y : Fin 2 → ℝ := ![2*T+1, x 1]
  have hx0 := abs_le.mp (hx 0)
  refine ⟨y, ?_, ?_⟩
  · intro hy
    have h := (hbox (mem_image_of_mem e hy)) 0
    simp only [Equiv.apply_symm_apply] at h
    change |2*T+1| ≤ T at h
    have := (abs_le.mp h).2
    linarith
  · have hs := planarSquaredDist_eq_dist_sq x y
    have hsq : planarSquaredDist x y = (x 0-(2*T+1))^2 := by
      simp [planarSquaredDist,y]
    rw [hsq] at hs
    have hd := dist_nonneg (x := e.symm x) (y := e.symm y)
    nlinarith

theorem planar_compl_nonempty_of_coordinateBox {T : ℝ} (hT : 0 ≤ T)
    {E : Set (WithLp 2 (Fin 2 → ℝ))}
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T) :
    Eᶜ.Nonempty := by
  have hz : (0 : Fin 2 → ℝ) ∈ planarCoordinateBox T := by
    intro j
    simpa using hT
  obtain ⟨y,hy,_⟩ := planar_bounded_search_witness hT hbox hz
  exact ⟨(WithLp.equiv 2 (Fin 2 → ℝ)).symm y,hy⟩

theorem planar_infDist_compl_le_of_coordinateBox {T : ℝ} (hT : 0 ≤ T)
    {E : Set (WithLp 2 (Fin 2 → ℝ))}
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    {x : Fin 2 → ℝ} (hx : x ∈ planarCoordinateBox T) :
    Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x) Eᶜ ≤ 3*T+1 := by
  obtain ⟨y,hy,hd⟩ := planar_bounded_search_witness hT hbox hx
  exact (Metric.infDist_le_dist_of_mem hy).trans hd

theorem planar_near_point_mem_coordinateBox {T R : ℝ}
    {x y : Fin 2 → ℝ} (hx : x ∈ planarCoordinateBox T)
    (hd : dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x)
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm y) ≤ R) :
    y ∈ planarCoordinateBox (T+R) := by
  intro j
  have hj := PiLp.dist_apply_le ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x)
    ((WithLp.equiv 2 (Fin 2 → ℝ)).symm y) j
  simp only [WithLp.equiv_symm_pi_apply, Real.dist_eq] at hj
  have hs : |y j-x j| ≤ R := by
    rw [abs_sub_comm]
    exact hj.trans hd
  calc
    |y j| = |x j+(y j-x j)| := by congr 1; ring
    _ ≤ |x j|+|y j-x j| := abs_add _ _
    _ ≤ T+R := add_le_add (hx j) hs

theorem planar_nearest_compl_mem_searchBox {T : ℝ} (hT : 0 ≤ T)
    {E : Set (WithLp 2 (Fin 2 → ℝ))}
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    {x y : Fin 2 → ℝ} (hx : x ∈ planarCoordinateBox T)
    (hmin : Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x) Eᶜ =
      dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x)
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm y)) :
    y ∈ planarCoordinateBox (4*T+1) := by
  have hd := planar_infDist_compl_le_of_coordinateBox hT hbox hx
  rw [hmin] at hd
  convert planar_near_point_mem_coordinateBox hx hd using 1 <;> ring

theorem planar_infDist_compl_attained_in_searchBox {T : ℝ} (hT : 0 ≤ T)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    {x : Fin 2 → ℝ} (hx : x ∈ planarCoordinateBox T) :
    ∃ y : Fin 2 → ℝ, y ∈ planarCoordinateBox (4*T+1) ∧
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm y ∉ E ∧
      Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x) Eᶜ =
        dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x)
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm y) := by
  let e := WithLp.equiv 2 (Fin 2 → ℝ)
  obtain ⟨y,hy,he⟩ := ho.isClosed_compl.exists_infDist_eq_dist
    (planar_compl_nonempty_of_coordinateBox hT hbox) (e.symm x)
  have he' : Metric.infDist (e.symm x) Eᶜ = dist (e.symm x) (e.symm (e y)) := by
    simpa only [Equiv.symm_apply_apply] using he
  refine ⟨e y,planar_nearest_compl_mem_searchBox hT hbox hx he',?_,he'⟩
  simpa only [Equiv.symm_apply_apply] using hy

end PaperI
