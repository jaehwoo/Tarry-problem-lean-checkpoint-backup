import PaperILean.PlanarBoundedSearch

/-! The exact restricted minimum, including zero distance. The reverse
direction uses the independently established localized global minimizer. -/

noncomputable section
namespace PaperI
open Set

theorem planar_infDist_compl_bounded_squared_minimum_iff
    {T : ℝ} (hT : 0 ≤ T)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    {x : Fin 2 → ℝ} (hx : x ∈ planarCoordinateBox T) (r : ℝ) :
    r = Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x) Eᶜ ↔
      0 ≤ r ∧
      (∃ y : Fin 2 → ℝ, y ∈ planarCoordinateBox (4*T+1) ∧
        (WithLp.equiv 2 (Fin 2 → ℝ)).symm y ∉ E ∧
        r^2 = planarSquaredDist x y) ∧
      ∀ y : Fin 2 → ℝ, y ∈ planarCoordinateBox (4*T+1) →
        (WithLp.equiv 2 (Fin 2 → ℝ)).symm y ∉ E →
        r^2 ≤ planarSquaredDist x y := by
  let e := WithLp.equiv 2 (Fin 2 → ℝ)
  obtain ⟨y,hy,hyE,hmin⟩ := planar_infDist_compl_attained_in_searchBox hT ho hbox hx
  constructor
  · intro hr
    refine ⟨hr ▸ Metric.infDist_nonneg, ⟨y,hy,hyE,?_⟩,?_⟩
    · rw [planarSquaredDist_eq_dist_sq,hr,hmin]
    · intro v _ hv
      rw [planarSquaredDist_eq_dist_sq,hr]
      exact pow_le_pow_left₀ Metric.infDist_nonneg (Metric.infDist_le_dist_of_mem hv) 2
  · rintro ⟨hr,⟨v,_,hv,he⟩,hall⟩
    have hlo := Metric.infDist_le_dist_of_mem (x:=e.symm x) (s:=Eᶜ) hv
    have hhi := hall y hy hyE
    rw [planarSquaredDist_eq_dist_sq] at he hhi
    rw [hmin] at hlo ⊢
    nlinarith [dist_nonneg (x:=e.symm x) (y:=e.symm y),
      dist_nonneg (x:=e.symm x) (y:=e.symm v)]

def planarBoundedSquaredDistanceGraph (S : Set (Fin 2 → ℝ)) (T : ℝ) :
    Set ((Unit ⊕ Fin 2) → ℝ) :=
  {v | 0 ≤ T ∧ (fun i => v (Sum.inr i)) ∈ planarCoordinateBox T ∧
    0 ≤ v (Sum.inl ()) ∧
    (∃ y, y ∈ planarCoordinateBox (4*T+1) ∧ y ∉ S ∧
      v (Sum.inl ())^2 = planarSquaredDist (fun i => v (Sum.inr i)) y) ∧
    ∀ y, y ∈ planarCoordinateBox (4*T+1) → y ∉ S →
      v (Sum.inl ())^2 ≤ planarSquaredDist (fun i => v (Sum.inr i)) y}

def planarBoxDistanceGraph (E : Set (WithLp 2 (Fin 2 → ℝ))) (T : ℝ) :
    Set ((Unit ⊕ Fin 2) → ℝ) :=
  {v | 0 ≤ T ∧ (fun i => v (Sum.inr i)) ∈ planarCoordinateBox T ∧
    v (Sum.inl ()) = Metric.infDist
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i => v (Sum.inr i))) Eᶜ}

theorem planarBoxDistanceGraph_eq_boundedSquaredDistanceGraph
    {T : ℝ} {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T) :
    planarBoxDistanceGraph E T = planarBoundedSquaredDistanceGraph
      ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) T := by
  ext v
  change (0 ≤ T ∧ _ ∧ _) ↔ (0 ≤ T ∧ _ ∧ _)
  apply and_congr_right
  intro hT
  apply and_congr_right
  intro hx
  rw [planar_infDist_compl_bounded_squared_minimum_iff hT ho hbox hx]
  simp

theorem planarBoxDistanceGraph_zero_of_not_mem
    {T : ℝ} (hT : 0 ≤ T) {E : Set (WithLp 2 (Fin 2 → ℝ))}
    {x : Fin 2 → ℝ} (hx : x ∈ planarCoordinateBox T)
    (hxe : (WithLp.equiv 2 (Fin 2 → ℝ)).symm x ∉ E) :
    Sum.elim (fun _ : Unit => (0 : ℝ)) x ∈ planarBoxDistanceGraph E T := by
  refine ⟨hT,hx,?_⟩
  exact (Metric.infDist_zero_of_mem hxe).symm

end PaperI
