import PaperILean.MonotonePlanarArcVariation

/-! I1261: cumulative *Euclidean* arclength, defined by the supremum of
polygonal sums. Coordinate variation only bounds this length; it is not
substituted for it. Flat segments and degenerate intervals are allowed. -/

noncomputable section
namespace PaperI
open Set

def planarEuclideanLength (γ : ℝ → Fin 2 → ℝ) (a b : ℝ) : ℝ :=
  (eVariationOn (fun t => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t)) (Icc a b)).toReal

theorem planar_euclidean_length_nonneg (γ : ℝ → Fin 2 → ℝ) (a b : ℝ) :
    0 ≤ planarEuclideanLength γ a b := ENNReal.toReal_nonneg

theorem planar_euclidean_length_self (γ : ℝ → Fin 2 → ℝ) (a : ℝ) :
    planarEuclideanLength γ a a = 0 := by
  simp [planarEuclideanLength]

theorem monotone_planar_arc_boundedVariation {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b)) :
    BoundedVariationOn (fun t => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t)) (Icc a b) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (monotone_planar_arc_eVariation_le hab hm)

theorem planar_euclidean_length_le_coordinate_variation {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b)) :
    planarEuclideanLength γ a b ≤ |γ b 0-γ a 0|+|γ b 1-γ a 1| :=
  ENNReal.toReal_le_of_le_ofReal (by positivity) (monotone_planar_arc_eVariation_le hab hm)

theorem planar_coordinate_monotone_restrict {γ : ℝ → Fin 2 → ℝ} {a b s t : ℝ}
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∀ i, MonotoneOn (fun t => γ t i) (Icc s t) ∨
      AntitoneOn (fun t => γ t i) (Icc s t) := by
  intro i
  exact (hm i).imp (fun h => h.mono (Icc_subset_Icc hs.1 ht.2))
    (fun h => h.mono (Icc_subset_Icc hs.1 ht.2))

theorem planar_euclidean_length_add {γ : ℝ → Fin 2 → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a c) ∨
      AntitoneOn (fun t => γ t i) (Icc a c)) :
    planarEuclideanLength γ a b + planarEuclideanLength γ b c =
      planarEuclideanLength γ a c := by
  let f := fun t => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t)
  have hf : BoundedVariationOn f (Icc a c) :=
    monotone_planar_arc_boundedVariation (hab.trans hbc) hm
  have hsum : eVariationOn f (Icc a b) + eVariationOn f (Icc b c) =
      eVariationOn f (Icc a c) := by
    simpa only [univ_inter] using eVariationOn.Icc_add_Icc f (s := univ) hab hbc (mem_univ b)
  simpa only [planarEuclideanLength, ENNReal.toReal_add
    (hf.mono (Icc_subset_Icc le_rfl hbc)) (hf.mono (Icc_subset_Icc hab le_rfl))] using
    congrArg ENNReal.toReal hsum

theorem planar_arclength_clock_increment {γ : ℝ → Fin 2 → ℝ} {a b s t : ℝ}
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    planarEuclideanLength γ a t - planarEuclideanLength γ a s =
      planarEuclideanLength γ s t := by
  have h := planar_euclidean_length_add hs.1 hst
    (planar_coordinate_monotone_restrict hm ⟨le_rfl,hs.1.trans hs.2⟩ ht)
  linarith

theorem planar_arclength_clock_monotone {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b)) :
    MonotoneOn (planarEuclideanLength γ a) (Icc a b) := by
  intro s hs t ht hst
  have := planar_arclength_clock_increment hm hs ht hst
  linarith [planar_euclidean_length_nonneg γ s t]

theorem planar_arclength_clock_dist_le_coordinate_clock {γ : ℝ → Fin 2 → ℝ} {a b s t : ℝ}
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    dist (planarEuclideanLength γ a s) (planarEuclideanLength γ a t) ≤
      dist (planarCoordinateVariationClock γ a s) (planarCoordinateVariationClock γ a t) := by
  wlog hst : t ≤ s generalizing s t
  · simpa only [dist_comm] using this ht hs (le_of_not_ge hst)
  rw [Real.dist_eq,Real.dist_eq,
    abs_of_nonneg (sub_nonneg.mpr (planar_arclength_clock_monotone hm ht hs hst)),
    abs_of_nonneg (sub_nonneg.mpr (planar_coordinate_clock_monotone hm ht hs hst)),
    planar_arclength_clock_increment hm ht hs hst,planar_coordinate_clock_increment hm ht hs hst]
  exact planar_euclidean_length_le_coordinate_variation hst
    (planar_coordinate_monotone_restrict hm ht hs)

theorem planar_arclength_clock_continuous {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b)) :
    ContinuousOn (planarEuclideanLength γ a) (Icc a b) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousOn_iff.mp (planar_coordinate_clock_continuous hc) t ht ε hε
  exact ⟨δ,hδ,fun s hs hst =>
    (planar_arclength_clock_dist_le_coordinate_clock hm hs ht).trans_lt (hd s hs hst)⟩

theorem planar_dist_le_arclength_clock {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b))
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) :
    dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ s))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t)) ≤
      |planarEuclideanLength γ a s-planarEuclideanLength γ a t| := by
  wlog hst : t ≤ s generalizing s t
  · simpa only [dist_comm,abs_sub_comm] using this t ht s hs (le_of_not_ge hst)
  rw [abs_of_nonneg (sub_nonneg.mpr (planar_arclength_clock_monotone hm ht hs hst)),
    planar_arclength_clock_increment hm ht hs hst]
  exact (monotone_planar_arc_boundedVariation hst
    (planar_coordinate_monotone_restrict hm ht hs)).dist_le ⟨hst,le_rfl⟩ ⟨le_rfl,hst⟩

theorem planar_arclength_zero_implies_constant {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b))
    (hz : planarEuclideanLength γ a b = 0) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, γ s = γ t := by
  intro s hs t ht
  have hd := (monotone_planar_arc_boundedVariation hab hm).dist_le hs ht
  change dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ s))
    ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t)) ≤ planarEuclideanLength γ a b at hd
  rw [hz] at hd
  exact (WithLp.equiv 2 (Fin 2 → ℝ)).symm.injective (dist_le_zero.mp hd)

end PaperI
