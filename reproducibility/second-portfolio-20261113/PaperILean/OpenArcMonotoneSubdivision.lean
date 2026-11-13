import PaperILean.PublishedOpenMonotoneCuts
import PaperILean.ClosedMonotoneArc

/-! I1261: split first on the open domain, then complete bounded monotone pieces.
No continuity at the original outer endpoints is used. Interior cut values are
retained, and the closed images have exactly the closure of the old open image.
This applies to supplied bounded-format charts, not yet to all actual boundary cells. -/
noncomputable section
namespace PaperI
open Set

theorem exists_adjacent_interval_of_mem_Ioo_partition
    (t : ℕ → ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (t 0) (t n)) :
    ∃ j < n, x ∈ Icc (t j) (t (j + 1)) := by
  induction n with
  | zero => exact (lt_irrefl _ (hx.1.trans hx.2)).elim
  | succ n ih =>
    by_cases h : x < t n
    · obtain ⟨j, hj, hxj⟩ := ih ⟨hx.1, h⟩
      exact ⟨j, hj.trans (Nat.lt_succ_self n), hxj⟩
    · exact ⟨n, Nat.lt_succ_self n, le_of_not_gt h, hx.2.le⟩

/-- Original values at interior cuts cannot be discarded when closing pieces. -/
theorem closedMonotoneArc_eq_at_interior_cut {κ : Type*} {γ : ℝ → κ → ℝ}
    {a b u v x : ℝ} (hc : ContinuousOn γ (Ioo a b)) (huv : u < v)
    (hxuv : x ∈ Icc u v) (hxab : x ∈ Ioo a b) :
    closedMonotoneArc γ u v x = γ x := by
  have hcx : ContinuousAt γ x := hc.continuousAt (isOpen_Ioo.mem_nhds hxab)
  funext i
  apply extendFrom_eq (by simpa only [closure_Ioo huv.ne] using hxuv)
  exact ((continuous_apply i).continuousAt.comp hcx).continuousWithinAt

theorem closed_monotone_subdivision_image_eq_closure
    {κ : Type*} {γ : ℝ → κ → ℝ} {a b : ℝ} (n : ℕ) (t : ℕ → ℝ)
    (ht0 : t 0 = a) (htn : t n = b) (ht : MonotoneOn t (Icc 0 n))
    (hc : ContinuousOn γ (Ioo a b))
    (hm : ∀ j < n, t j < t (j + 1) ∧ ∀ i,
      MonotoneOn (fun x => γ x i) (Ioo (t j) (t (j + 1))) ∨
        AntitoneOn (fun x => γ x i) (Ioo (t j) (t (j + 1))))
    (hlo : ∀ i, BddBelow ((fun x => γ x i) '' Ioo a b))
    (hhi : ∀ i, BddAbove ((fun x => γ x i) '' Ioo a b)) :
    (⋃ j : Fin n, closedMonotoneArc γ (t j.val) (t (j.val + 1)) ''
      Icc (t j.val) (t (j.val + 1))) = closure (γ '' Ioo a b) := by
  have hsub (j : Fin n) : Ioo (t j.val) (t (j.val + 1)) ⊆ Ioo a b := by
    have h0 := ht ⟨le_rfl, Nat.zero_le n⟩ ⟨Nat.zero_le _, j.isLt.le⟩ (Nat.zero_le _)
    have hn := ht ⟨Nat.zero_le _, j.isLt⟩ ⟨Nat.zero_le n, le_rfl⟩ j.isLt
    rw [ht0] at h0
    rw [htn] at hn
    exact Ioo_subset_Ioo h0 hn
  have hcj (j : Fin n) := closedMonotoneArc_continuousOn (hm j.val j.isLt).1
    (hc.mono (hsub j)) (hm j.val j.isLt).2
    (fun i => (hlo i).mono (image_mono (hsub j)))
    (fun i => (hhi i).mono (image_mono (hsub j)))
  have himg (j : Fin n) := closedMonotoneArc_image_eq_closure (hm j.val j.isLt).1
    (hc.mono (hsub j)) (hm j.val j.isLt).2
    (fun i => (hlo i).mono (image_mono (hsub j)))
    (fun i => (hhi i).mono (image_mono (hsub j)))
  apply Subset.antisymm
  · apply iUnion_subset
    intro j
    rw [himg j]
    exact closure_mono (image_mono (hsub j))
  · apply closure_minimal
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨j, hj, hxj⟩ := exists_adjacent_interval_of_mem_Ioo_partition t n
        (by simpa only [ht0, htn] using hx)
      apply mem_iUnion.mpr
      exact ⟨⟨j, hj⟩, x, hxj, closedMonotoneArc_eq_at_interior_cut hc (hm j hj).1 hxj hx⟩
    · exact isClosed_iUnion_of_finite fun j => (isCompact_Icc.image_of_continuousOn (hcj j)).isClosed

/-- The piece count precedes every curve, interval and range bound. -/
theorem published_bounded_open_arc_closed_monotone_cover
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity)
    (κ : Type) [Fintype κ] (s D : ℕ) :
    ∃ M : ℕ, ∀ (γ : ℝ → κ → ℝ) (a b : ℝ), a < b →
      ContinuousOn γ (Ioo a b) →
      (∀ i, ∃ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
        A.card ≤ s ∧ (∀ q ∈ A, q.totalDegree ≤ D) ∧ PolynomialSignDetermined A S ∧
        ∀ x ∈ Ioo a b, ∀ y : ℝ, ![x,y] ∈ S ↔ y = γ x i) →
      (∀ i, BddBelow ((fun x => γ x i) '' Ioo a b)) →
      (∀ i, BddAbove ((fun x => γ x i) '' Ioo a b)) →
      ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ M ∧ t 0 = a ∧ t n = b ∧
        MonotoneOn t (Icc 0 n) ∧
        (∀ j < n, t j < t (j + 1) ∧
          ContinuousOn (closedMonotoneArc γ (t j) (t (j + 1))) (Icc (t j) (t (j + 1))) ∧
          ∀ i, MonotoneOn (fun x => closedMonotoneArc γ (t j) (t (j + 1)) x i)
              (Icc (t j) (t (j + 1))) ∨
            AntitoneOn (fun x => closedMonotoneArc γ (t j) (t (j + 1)) x i)
              (Icc (t j) (t (j + 1)))) ∧
        (⋃ j : Fin n, closedMonotoneArc γ (t j.val) (t (j.val + 1)) ''
          Icc (t j.val) (t (j.val + 1))) = closure (γ '' Ioo a b) := by
  obtain ⟨M, hM⟩ := published_bounded_sign_format_strict_open_common_partition
    hCell hHardt hQE hMono κ s D
  refine ⟨M, ?_⟩
  intro γ a b hab hc hgraph hlo hhi
  obtain ⟨n, t, hn, ht0, htn, ht, hm⟩ := hM (fun i x => γ x i) a b hab.le
    (fun i => (continuous_apply i).comp_continuousOn hc) hgraph
  refine ⟨n, t, hn, ht0, htn, ht, ?_,
    closed_monotone_subdivision_image_eq_closure n t ht0 htn ht hc hm hlo hhi⟩
  intro j hj
  have h0 := ht ⟨le_rfl, Nat.zero_le n⟩ ⟨Nat.zero_le _, hj.le⟩ (Nat.zero_le _)
  have hn := ht ⟨Nat.zero_le _, hj⟩ ⟨Nat.zero_le n, le_rfl⟩ hj
  rw [ht0] at h0
  rw [htn] at hn
  have hsub : Ioo (t j) (t (j + 1)) ⊆ Ioo a b := Ioo_subset_Ioo h0 hn
  have hlj := fun i => (hlo i).mono (image_mono hsub)
  have hhj := fun i => (hhi i).mono (image_mono hsub)
  exact ⟨(hm j hj).1, closedMonotoneArc_continuousOn (hm j hj).1 (hc.mono hsub)
    (hm j hj).2 hlj hhj,
    closedMonotoneArc_coordinate_monotone (hm j hj).1 (hc.mono hsub) (hm j hj).2 hlj hhj⟩

/-- Actual Euclidean local-frontier membership, still conditional on supplied charts. -/
theorem published_planar_open_arc_closed_localFrontier_cover
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hMono : PublishedOneVariableMonotonicity) (s D : ℕ) :
    ∃ M : ℕ, ∀ (γ : ℝ → Fin 2 → ℝ) (a b : ℝ), a < b →
      ContinuousOn γ (Ioo a b) →
      (∀ i, ∃ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
        A.card ≤ s ∧ (∀ q ∈ A, q.totalDegree ≤ D) ∧ PolynomialSignDetermined A S ∧
        ∀ x ∈ Ioo a b, ∀ y : ℝ, ![x,y] ∈ S ↔ y = γ x i) →
      ∀ (E : Set (WithLp 2 (Fin 2 → ℝ))) (z : WithLp 2 (Fin 2 → ℝ)) (R : ℝ),
      (∀ x ∈ Ioo a b, (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ x) ∈
        frontier E ∩ Metric.closedBall z R) →
      ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ M ∧ t 0 = a ∧ t n = b ∧
        MonotoneOn t (Icc 0 n) ∧
        (∀ j < n, t j < t (j + 1) ∧
          ContinuousOn (closedMonotoneArc γ (t j) (t (j + 1))) (Icc (t j) (t (j + 1))) ∧
          ∀ i, MonotoneOn (fun x => closedMonotoneArc γ (t j) (t (j + 1)) x i)
              (Icc (t j) (t (j + 1))) ∨
            AntitoneOn (fun x => closedMonotoneArc γ (t j) (t (j + 1)) x i)
              (Icc (t j) (t (j + 1)))) ∧
        (⋃ j : Fin n, closedMonotoneArc γ (t j.val) (t (j.val + 1)) ''
          Icc (t j.val) (t (j.val + 1))) = closure (γ '' Ioo a b) ∧
        ∀ j < n, ∀ x ∈ Icc (t j) (t (j + 1)),
          (WithLp.equiv 2 (Fin 2 → ℝ)).symm (closedMonotoneArc γ (t j) (t (j + 1)) x) ∈
            frontier E ∩ Metric.closedBall z R := by
  obtain ⟨M, hM⟩ := published_bounded_open_arc_closed_monotone_cover hCell hHardt hQE hMono (Fin 2) s D
  refine ⟨M, ?_⟩
  intro γ a b hab hc hgraph E z R hmap
  obtain ⟨hlo, hhi⟩ := planar_open_arc_coordinate_bounds z R (fun x hx => (hmap x hx).2)
  obtain ⟨n, t, hn, ht0, htn, ht, hp, hcover⟩ := hM γ a b hab hc hgraph hlo hhi
  refine ⟨n, t, hn, ht0, htn, ht, hp, hcover, ?_⟩
  intro j hj x hx
  have hK : IsClosed ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ⁻¹'
      (frontier E ∩ Metric.closedBall z R)) :=
    (isClosed_frontier.inter Metric.isClosed_closedBall).preimage planarCoordinatesHomeomorph.symm.continuous
  have hmem : closedMonotoneArc γ (t j) (t (j + 1)) x ∈ closure (γ '' Ioo a b) := by
    rw [← hcover]
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, x, hx, rfl⟩
  exact closure_minimal (image_subset_iff.mpr hmap) hK hmem

end PaperI
