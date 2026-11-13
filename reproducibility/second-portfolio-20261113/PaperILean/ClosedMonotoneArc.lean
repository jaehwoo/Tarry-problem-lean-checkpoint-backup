import PaperILean.MonotoneOpenIntervalLimits
import PaperILean.LocalFrontierGeometry

/-! Endpoint completion of the manuscript's bounded coordinate-monotone pieces.
No cell decomposition or uniform count is assumed or produced here. The
extension retains the original parametrization on its whole open interval. -/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology

def closedMonotoneArc {κ : Type*} (γ : ℝ → κ → ℝ) (a b t : ℝ) (i : κ) : ℝ :=
  extendFrom (Ioo a b) (fun s => γ s i) t

theorem closedMonotoneArc_eq {κ : Type*} {γ : ℝ → κ → ℝ} {a b t : ℝ}
    (hc : ContinuousOn γ (Ioo a b)) (ht : t ∈ Ioo a b) :
    closedMonotoneArc γ a b t = γ t := by
  funext i
  exact extendFrom_extends ((continuous_apply i).comp_continuousOn hc) t ht

theorem closedMonotoneArc_continuousOn {κ : Type*} {γ : ℝ → κ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn γ (Ioo a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Ioo a b) ∨
      AntitoneOn (fun t => γ t i) (Ioo a b))
    (hlo : ∀ i, BddBelow ((fun t => γ t i) '' Ioo a b))
    (hhi : ∀ i, BddAbove ((fun t => γ t i) '' Ioo a b)) :
    ContinuousOn (closedMonotoneArc γ a b) (Icc a b) := by
  apply continuousOn_pi.mpr
  intro i
  exact bounded_monotone_extendFrom_continuousOn hab
    ((continuous_apply i).comp_continuousOn hc) (hm i) (hlo i) (hhi i)

theorem closedMonotoneArc_coordinate_monotone {κ : Type*} {γ : ℝ → κ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn γ (Ioo a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Ioo a b) ∨
      AntitoneOn (fun t => γ t i) (Ioo a b))
    (hlo : ∀ i, BddBelow ((fun t => γ t i) '' Ioo a b))
    (hhi : ∀ i, BddAbove ((fun t => γ t i) '' Ioo a b)) :
    ∀ i, MonotoneOn (fun t => closedMonotoneArc γ a b t i) (Icc a b) ∨
      AntitoneOn (fun t => closedMonotoneArc γ a b t i) (Icc a b) := by
  intro i
  exact monotone_or_antitone_extendFrom_Ioo hab
    ((continuous_apply i).comp_continuousOn hc) (hm i) (hlo i) (hhi i)

/-- A generic closed-interval completion has exactly the closure of the old image. -/
theorem closed_interval_extension_image_eq_closure {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] {f g : ℝ → Y} {a b : ℝ}
    (hab : a < b) (hg : ContinuousOn g (Icc a b)) (he : EqOn g f (Ioo a b)) :
    g '' Icc a b = closure (f '' Ioo a b) := by
  have hi : g '' Ioo a b = f '' Ioo a b := image_congr he
  apply Subset.antisymm
  · have hg' : ContinuousOn g (closure (Ioo a b)) := by simpa [closure_Ioo hab.ne] using hg
    simpa only [closure_Ioo hab.ne, hi] using hg'.image_closure
  · apply closure_minimal
    · rw [← hi]
      exact image_mono Ioo_subset_Icc_self
    · exact (isCompact_Icc.image_of_continuousOn hg).isClosed

theorem closedMonotoneArc_image_eq_closure {κ : Type*} {γ : ℝ → κ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn γ (Ioo a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Ioo a b) ∨
      AntitoneOn (fun t => γ t i) (Ioo a b))
    (hlo : ∀ i, BddBelow ((fun t => γ t i) '' Ioo a b))
    (hhi : ∀ i, BddAbove ((fun t => γ t i) '' Ioo a b)) :
    closedMonotoneArc γ a b '' Icc a b = closure (γ '' Ioo a b) :=
  closed_interval_extension_image_eq_closure hab
    (closedMonotoneArc_continuousOn hab hc hm hlo hhi)
    (fun _ ht => closedMonotoneArc_eq hc ht)

theorem closedMonotoneArc_mapsTo_closed {κ : Type*} {γ : ℝ → κ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn γ (Ioo a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Ioo a b) ∨
      AntitoneOn (fun t => γ t i) (Ioo a b))
    (hlo : ∀ i, BddBelow ((fun t => γ t i) '' Ioo a b))
    (hhi : ∀ i, BddAbove ((fun t => γ t i) '' Ioo a b))
    {K : Set (κ → ℝ)} (hK : IsClosed K) (hmap : MapsTo γ (Ioo a b) K) :
    MapsTo (closedMonotoneArc γ a b) (Icc a b) K := by
  apply image_subset_iff.mp
  rw [closedMonotoneArc_image_eq_closure hab hc hm hlo hhi]
  exact closure_minimal hmap.image_subset hK

theorem planar_open_arc_coordinate_bounds {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (z : WithLp 2 (Fin 2 → ℝ)) (R : ℝ)
    (hmap : ∀ t ∈ Ioo a b, (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t) ∈ Metric.closedBall z R) :
    (∀ i, BddBelow ((fun t => γ t i) '' Ioo a b)) ∧
      (∀ i, BddAbove ((fun t => γ t i) '' Ioo a b)) := by
  have hb (t : ℝ) (ht : t ∈ Ioo a b) (i : Fin 2) : |γ t i - z i| ≤ R := by
    have h := (PiLp.dist_apply_le ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t)) z i).trans
      (Metric.mem_closedBall.mp (hmap t ht))
    simpa only [WithLp.equiv_symm_pi_apply, Real.dist_eq] using h
  constructor
  · intro i
    refine ⟨z i - R, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have h := (abs_le.mp (hb t ht i)).1
    linarith
  · intro i
    refine ⟨z i + R, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have h := (abs_le.mp (hb t ht i)).2
    linarith

/-- Endpoint completion stays in the actual local frontier, not merely in E's closure. -/
theorem closedMonotoneArc_mem_localFrontier
    {γ : ℝ → Fin 2 → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn γ (Ioo a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Ioo a b) ∨
      AntitoneOn (fun t => γ t i) (Ioo a b))
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (z : WithLp 2 (Fin 2 → ℝ)) (R : ℝ)
    (hmap : ∀ t ∈ Ioo a b, (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t) ∈
      frontier E ∩ Metric.closedBall z R) :
    ∀ t ∈ Icc a b, (WithLp.equiv 2 (Fin 2 → ℝ)).symm (closedMonotoneArc γ a b t) ∈
      frontier E ∩ Metric.closedBall z R := by
  obtain ⟨hlo, hhi⟩ := planar_open_arc_coordinate_bounds z R (fun t ht => (hmap t ht).2)
  let K := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ⁻¹' (frontier E ∩ Metric.closedBall z R)
  have hK : IsClosed K := (isClosed_frontier.inter Metric.isClosed_closedBall).preimage
    planarCoordinatesHomeomorph.symm.continuous
  exact closedMonotoneArc_mapsTo_closed hab hc hm hlo hhi hK hmap

theorem closed_interval_extension_unique {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : ℝ → Y} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (he : EqOn f g (Ioo a b)) : EqOn f g (Icc a b) :=
  he.of_subset_closure hf hg Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])

/-- Constant arcs remain point arcs, including their newly attached endpoints. -/
theorem closedMonotoneArc_const {κ : Type*} (c : κ → ℝ) {a b : ℝ} (hab : a < b) :
    EqOn (closedMonotoneArc (fun _ => c) a b) (fun _ => c) (Icc a b) := by
  have hm : ∀ i : κ, MonotoneOn (fun _ : ℝ => c i) (Ioo a b) ∨
      AntitoneOn (fun _ : ℝ => c i) (Ioo a b) := fun _ => Or.inl (fun _ _ _ _ _ => le_rfl)
  have hlo : ∀ i : κ, BddBelow ((fun _ : ℝ => c i) '' Ioo a b) := by
    intro i; exact ⟨c i, by rintro _ ⟨t, ht, rfl⟩; exact le_rfl⟩
  have hhi : ∀ i : κ, BddAbove ((fun _ : ℝ => c i) '' Ioo a b) := by
    intro i; exact ⟨c i, by rintro _ ⟨t, ht, rfl⟩; exact le_rfl⟩
  exact closed_interval_extension_unique hab
    (closedMonotoneArc_continuousOn hab continuousOn_const hm hlo hhi) continuousOn_const
    (fun _ ht => closedMonotoneArc_eq continuousOn_const ht)

end PaperI
