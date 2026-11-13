import PaperILean.ControlledScalarMesh
import PaperILean.PlanarMacroscopicArc
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! I1261: coordinatewise monotone/antitone arcs, including points and flat
segments. Distances and total variation in the conclusions are Euclidean.
The clock below is the sum of coordinate variations from the left endpoint. -/

noncomputable section
namespace PaperI
open Set
open scoped BigOperators

def planarCoordinateVariationClock (γ : ℝ → Fin 2 → ℝ) (a t : ℝ) : ℝ :=
  |γ t 0-γ a 0|+|γ t 1-γ a 1|

theorem monotone_or_antitone_abs_increment {g : ℝ → ℝ} {a b s t : ℝ}
    (hg : MonotoneOn g (Icc a b) ∨ AntitoneOn g (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    |g t-g s|=|g t-g a|-|g s-g a| := by
  have ha : a ∈ Icc a b := ⟨le_rfl,hs.1.trans hs.2⟩
  rcases hg with hg | hg
  · rw [abs_of_nonneg (sub_nonneg.mpr (hg hs ht hst)),
      abs_of_nonneg (sub_nonneg.mpr (hg ha ht ht.1)),
      abs_of_nonneg (sub_nonneg.mpr (hg ha hs hs.1))]
    ring
  · rw [abs_of_nonpos (sub_nonpos.mpr (hg hs ht hst)),
      abs_of_nonpos (sub_nonpos.mpr (hg ha ht ht.1)),
      abs_of_nonpos (sub_nonpos.mpr (hg ha hs hs.1))]
    ring

theorem planar_coordinate_clock_increment {γ : ℝ → Fin 2 → ℝ} {a b s t : ℝ}
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    planarCoordinateVariationClock γ a t-planarCoordinateVariationClock γ a s =
      |γ t 0-γ s 0|+|γ t 1-γ s 1| := by
  rw [monotone_or_antitone_abs_increment (hm 0) hs ht hst,
    monotone_or_antitone_abs_increment (hm 1) hs ht hst]
  unfold planarCoordinateVariationClock
  ring

theorem planar_coordinate_clock_monotone {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b)) :
    MonotoneOn (planarCoordinateVariationClock γ a) (Icc a b) := by
  intro s hs t ht hst
  exact sub_nonneg.mp ((planar_coordinate_clock_increment hm hs ht hst).symm ▸
    add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem planar_coordinate_clock_continuous {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hc : ContinuousOn γ (Icc a b)) :
    ContinuousOn (planarCoordinateVariationClock γ a) (Icc a b) :=
  (((continuous_apply 0).comp_continuousOn hc).sub continuousOn_const).abs.add
    (((continuous_apply 1).comp_continuousOn hc).sub continuousOn_const).abs

theorem planar_dist_le_coordinate_clock {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b))
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) :
    dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ s))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t)) ≤
      |planarCoordinateVariationClock γ a s-planarCoordinateVariationClock γ a t| := by
  wlog hst : t ≤ s generalizing s t
  · simpa only [dist_comm,abs_sub_comm] using this t ht s hs (le_of_not_ge hst)
  rw [abs_of_nonneg (sub_nonneg.mpr (planar_coordinate_clock_monotone hm ht hs hst)),
    planar_coordinate_clock_increment hm ht hs hst]
  exact planar_euclidean_dist_le_coordinate_sum (γ s) (γ t)

theorem eVariationOn_le_of_pointwise_dist_le {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (γ : ℝ → X) (f : ℝ → Y) (S : Set ℝ)
    (hd : ∀ s ∈ S, ∀ t ∈ S, dist (γ s) (γ t) ≤ dist (f s) (f t)) :
    eVariationOn γ S ≤ eVariationOn f S := by
  apply iSup_le
  rintro ⟨n,u,hu,hs⟩
  exact (Finset.sum_le_sum (fun i _ => by
    rw [edist_dist,edist_dist]
    exact ENNReal.ofReal_le_ofReal (hd _ (hs _) _ (hs _)))).trans
    (eVariationOn.sum_le f n hu hs)

/-- Actual Euclidean total variation, not the variation in the supremum norm. -/
theorem monotone_planar_arc_eVariation_le {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b)) :
    eVariationOn (fun t => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t)) (Icc a b) ≤
      ENNReal.ofReal (|γ b 0-γ a 0|+|γ b 1-γ a 1|) := by
  refine (eVariationOn_le_of_pointwise_dist_le _ (planarCoordinateVariationClock γ a)
    (Icc a b) (fun s hs t ht => ?_)).trans ?_
  · simpa only [Real.dist_eq] using planar_dist_le_coordinate_clock hm s hs t ht
  · simpa [planarCoordinateVariationClock] using
      (planar_coordinate_clock_monotone hm).eVariationOn_le
        (a := a) (b := b) ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩

theorem monotone_planar_arc_finite_mesh {γ : ℝ → Fin 2 → ℝ} {a b W : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b)) :
    ∃ n : ℕ, 0 < n ∧ ∃ times : Fin n → ℝ,
      (∀ i, times i ∈ Icc a b) ∧
      (n : ℝ)*W ≤ |γ b 0-γ a 0|+|γ b 1-γ a 1|+W ∧
      ∀ t ∈ Icc a b, ∃ i,
        dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t))
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ (times i))) < W := by
  simpa [planarCoordinateVariationClock] using controlled_scalar_finite_mesh
    (fun t => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t))
    (planarCoordinateVariationClock γ a) hab hW
    (planar_coordinate_clock_continuous hc) (planar_coordinate_clock_monotone hm)
    (planar_dist_le_coordinate_clock hm)

theorem planar_endpoint_coordinate_variation_le_four_radius
    (γ : ℝ → Fin 2 → ℝ) (a b : ℝ) (z : EuclideanSpace ℝ (Fin 2)) (R : ℝ)
    (ha : (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ a) ∈ Metric.closedBall z R)
    (hb : (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ b) ∈ Metric.closedBall z R) :
    |γ b 0-γ a 0|+|γ b 1-γ a 1| ≤ 4*R := by
  have hd : dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ b))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ a)) ≤ 2*R := by
    have h := dist_triangle ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ b)) z
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ a))
    rw [dist_comm z] at h
    linarith [Metric.mem_closedBall.mp ha,Metric.mem_closedBall.mp hb]
  have hi (i : Fin 2) : |γ b i-γ a i| ≤ 2*R := by
    have h := PiLp.dist_apply_le ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ b))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ a)) i
    have h' : |γ b i-γ a i| ≤ dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ b))
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ a)) := by
      simpa only [WithLp.equiv_symm_pi_apply,Real.dist_eq] using h
    exact h'.trans hd
  linarith [hi 0,hi 1]

end PaperI
