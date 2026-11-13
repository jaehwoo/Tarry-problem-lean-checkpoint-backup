import PaperILean.BufferedDistanceBandGeometry

/-! I1259: the actual Euclidean distance to the closed complement, expressed
by squared polynomial distances. The nonempty-complement premise is derived
from boundedness for the manuscript application. No compactness of E or Eᶜ
and no attainment of a component diameter is assumed. -/

noncomputable section
namespace PaperI
open Set

def planarSquaredDist (x y : Fin 2 → ℝ) : ℝ :=
  (x 0-y 0)^2+(x 1-y 1)^2

theorem planarSquaredDist_nonneg (x y : Fin 2 → ℝ) : 0 ≤ planarSquaredDist x y := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem planarSquaredDist_eq_dist_sq (x y : Fin 2 → ℝ) :
    planarSquaredDist x y =
      dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x)
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm y)^2 := by
  rw [PiLp.dist_eq_of_L2,Fin.sum_univ_two]
  simp only [WithLp.equiv_symm_pi_apply,Real.dist_eq,sq_abs]
  exact (Real.sq_sqrt (planarSquaredDist_nonneg x y)).symm

theorem planar_compl_nonempty_of_isBounded
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (hE : Bornology.IsBounded E) : Eᶜ.Nonempty := by
  by_contra hn
  have he : E = univ := by
    apply eq_univ_of_forall
    intro x
    by_contra hx
    exact hn ⟨x,hx⟩
  exact NormedSpace.unbounded_univ ℝ (WithLp 2 (Fin 2 → ℝ)) (he ▸ hE)

/-- Exact graph-of-distance formula, including distance zero. -/
theorem planar_infDist_compl_squared_minimum_iff
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (hE : IsOpen E) (hne : Eᶜ.Nonempty)
    (x : Fin 2 → ℝ) (r : ℝ) :
    r = Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x) Eᶜ ↔
      0 ≤ r ∧ ∃ y : Fin 2 → ℝ,
        (WithLp.equiv 2 (Fin 2 → ℝ)).symm y ∉ E ∧
        r^2 = planarSquaredDist x y ∧
        ∀ v : Fin 2 → ℝ, (WithLp.equiv 2 (Fin 2 → ℝ)).symm v ∉ E →
          r^2 ≤ planarSquaredDist x v := by
  let e := WithLp.equiv 2 (Fin 2 → ℝ)
  obtain ⟨y,hy,hmin⟩ := hE.isClosed_compl.exists_infDist_eq_dist hne (e.symm x)
  constructor
  · intro hr
    refine ⟨hr ▸ Metric.infDist_nonneg, e y,hy,?_,?_⟩
    · rw [planarSquaredDist_eq_dist_sq,Equiv.symm_apply_apply,hr]
      exact congrArg (fun t : ℝ => t^2) hmin
    · intro v hv
      rw [planarSquaredDist_eq_dist_sq,hr]
      exact pow_le_pow_left₀ Metric.infDist_nonneg (Metric.infDist_le_dist_of_mem hv) 2
  · rintro ⟨hr,y',hy',heq,hall⟩
    have hlo := Metric.infDist_le_dist_of_mem (x:=e.symm x) (s:=Eᶜ) hy'
    have hhi := hall (e y) hy
    rw [planarSquaredDist_eq_dist_sq] at heq hhi
    change r^2 ≤ dist (e.symm x) (e.symm (e y))^2 at hhi
    rw [e.symm_apply_apply] at hhi
    rw [hmin] at hlo ⊢
    nlinarith [dist_nonneg (x:=e.symm x) (y:=y),
      dist_nonneg (x:=e.symm x) (y:=e.symm y')]

def planarSquaredBand (S : Set (Fin 2 → ℝ)) (W : ℝ) : Set (Fin 2 → ℝ) :=
  {x | (∀ y, y ∉ S → W^2 < 4*planarSquaredDist x y) ∧
    ∃ y, y ∉ S ∧ planarSquaredDist x y < 16*W^2}

/-- The universal strict lower bound uses a nearest complement point; a
pointwise strict inequality alone would not control a nonattained infimum. -/
theorem bufferedDistanceBand_coordinates_eq_squaredBand
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (hE : IsOpen E) (hne : Eᶜ.Nonempty)
    {W : ℝ} (hW : 0 < W) :
    (WithLp.equiv 2 (Fin 2 → ℝ)) '' bufferedDistanceBand E W =
      planarSquaredBand ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) W := by
  let e := WithLp.equiv 2 (Fin 2 → ℝ)
  ext x
  have hmem (y : Fin 2 → ℝ) : y ∈ e '' E ↔ e.symm y ∈ E := by
    simp
  have hx : x ∈ e '' bufferedDistanceBand E W ↔
      W/2 < Metric.infDist (e.symm x) Eᶜ ∧ Metric.infDist (e.symm x) Eᶜ < 4*W :=
    by simp [bufferedDistanceBand]
  rw [hx]
  obtain ⟨y,hy,hmin⟩ := hE.isClosed_compl.exists_infDist_eq_dist hne (e.symm x)
  constructor
  · rintro ⟨hlo,hhi⟩
    refine ⟨?_, e y,?_,?_⟩
    · intro v hv
      have hd := Metric.infDist_le_dist_of_mem (x:=e.symm x) (show e.symm v ∈ Eᶜ from
        fun he => hv ((hmem v).mpr he))
      rw [planarSquaredDist_eq_dist_sq]
      nlinarith [sq_nonneg (dist (e.symm x) (e.symm v)-W/2)]
    · change e y ∉ e '' E
      simpa only [hmem,Equiv.symm_apply_apply] using hy
    · rw [planarSquaredDist_eq_dist_sq,Equiv.symm_apply_apply,← hmin]
      nlinarith [Metric.infDist_nonneg (x:=e.symm x) (s:=Eᶜ)]
  · rintro ⟨hlo,v,hv,hhi⟩
    have hy' : e y ∉ e '' E := by
      simpa only [hmem,Equiv.symm_apply_apply] using hy
    have hl := hlo (e y) hy'
    rw [planarSquaredDist_eq_dist_sq,Equiv.symm_apply_apply,← hmin] at hl
    have hd := Metric.infDist_le_dist_of_mem (x:=e.symm x)
      (show e.symm v ∈ Eᶜ from fun he => hv ((hmem v).mpr he))
    rw [planarSquaredDist_eq_dist_sq] at hhi
    have hn := Metric.infDist_nonneg (x:=e.symm x) (s:=Eᶜ)
    have hdn := dist_nonneg (x:=e.symm x) (y:=e.symm v)
    constructor <;> nlinarith

theorem bounded_bufferedDistanceBand_coordinates_eq_squaredBand
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (hE : IsOpen E) (hb : Bornology.IsBounded E)
    {W : ℝ} (hW : 0 < W) :
    (WithLp.equiv 2 (Fin 2 → ℝ)) '' bufferedDistanceBand E W =
      planarSquaredBand ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) W :=
  bufferedDistanceBand_coordinates_eq_squaredBand hE (planar_compl_nonempty_of_isBounded hb) hW

end PaperI
