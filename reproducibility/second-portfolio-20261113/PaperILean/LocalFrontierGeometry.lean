import PaperILean.UniformLocalFrontierFormat

/-! Exact Euclidean transport and compactness/empty-interior prerequisites.
Empty interior alone is not asserted to construct or count arc charts. -/
noncomputable section
namespace PaperI
open Set

theorem planarLocalFrontier_coordinates
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (z : WithLp 2 (Fin 2 → ℝ)) (R : ℝ) :
    (WithLp.equiv 2 (Fin 2 → ℝ)) '' (frontier E ∩ Metric.closedBall z R) =
      planarLocalFrontier ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E)
        ((WithLp.equiv 2 (Fin 2 → ℝ)) z) R := by
  let e := WithLp.equiv 2 (Fin 2 → ℝ)
  have hf : e '' frontier E = frontier (e '' E) :=
    planarCoordinatesHomeomorph.image_frontier E
  ext x
  have hm : x ∈ e '' (frontier E ∩ Metric.closedBall z R) ↔
      x ∈ frontier (e '' E) ∧ dist (e.symm x) z ≤ R := by
    rw [← hf]
    simp
  rw [hm]
  simp only [planarLocalFrontier, mem_setOf_eq, planarSquaredDist_eq_dist_sq,
    Equiv.symm_apply_apply]
  apply and_congr_right
  intro _
  constructor
  · intro h
    exact ⟨dist_nonneg.trans h, pow_le_pow_left₀ dist_nonneg h 2⟩
  · rintro ⟨hR, hsq⟩
    nlinarith [dist_nonneg (x := e.symm x) (y := z)]

theorem localFrontier_isCompact
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (z : WithLp 2 (Fin 2 → ℝ)) (R : ℝ) :
    IsCompact (frontier E ∩ Metric.closedBall z R) :=
  (isCompact_closedBall z R).inter_left isClosed_frontier

theorem localFrontier_interior_eq_empty
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (hE : IsOpen E)
    (z : WithLp 2 (Fin 2 → ℝ)) (R : ℝ) :
    interior (frontier E ∩ Metric.closedBall z R) = ∅ := by
  have hf : interior (frontier E) = ∅ := by
    simpa only [frontier_compl] using interior_frontier hE.isClosed_compl
  apply subset_empty_iff.mp
  exact hf ▸ interior_mono inter_subset_left

theorem localFrontier_open_subset_eq_empty
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (hE : IsOpen E)
    (z : WithLp 2 (Fin 2 → ℝ)) (R : ℝ)
    {U : Set (WithLp 2 (Fin 2 → ℝ))} (hU : IsOpen U)
    (hsub : U ⊆ frontier E ∩ Metric.closedBall z R) : U = ∅ := by
  have h := hU.subset_interior_iff.mpr hsub
  rw [localFrontier_interior_eq_empty hE z R] at h
  exact subset_empty_iff.mp h

theorem localFrontier_negative_radius
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (z : WithLp 2 (Fin 2 → ℝ))
    {R : ℝ} (hR : R < 0) : frontier E ∩ Metric.closedBall z R = ∅ := by
  simp [Metric.closedBall_eq_empty.mpr hR]

theorem localFrontier_zero_radius
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (z : WithLp 2 (Fin 2 → ℝ)) :
    frontier E ∩ Metric.closedBall z 0 = frontier E ∩ {z} := by
  rw [Metric.closedBall_zero]

/-- Bounds are chosen before E, its coefficients, the center, and every radius.
Openness/boundedness of E are unnecessary for this format-only prerequisite. -/
theorem published_uniform_localFrontier_format
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ sOut dOut : ℕ, ∀ (E : Set (WithLp 2 (Fin 2 → ℝ)))
      (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) →
      ∀ (z : WithLp 2 (Fin 2 → ℝ)) (R : ℝ),
      ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined B
          ((WithLp.equiv 2 (Fin 2 → ℝ)) '' (frontier E ∩ Metric.closedBall z R)) := by
  obtain ⟨sOut, dOut, h⟩ := published_bounded_sign_format_localFrontier_format hQE s D
  refine ⟨sOut, dOut, ?_⟩
  intro E A hc hd hE z R
  rw [planarLocalFrontier_coordinates]
  exact h A _ hc hd hE _ R

end PaperI
