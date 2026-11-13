import PaperILean.BufferedDistanceBandGeometry

/-! I1263, small-diameter branch. A concrete closed rectangle at the assigned
point has area W^2/4, lies inside E, and needs no derivative preparation.
The original constant centerline may have arbitrary vertical offset. -/

noncomputable section
namespace PaperI
open Set MeasureTheory

def bufferedPointRectangle (z : WithLp 2 (Fin 2 → ℝ)) (W : ℝ) :
    Set (WithLp 2 (Fin 2 → ℝ)) :=
  signedPlanarStrip 0 1 (fun _ => (WithLp.equiv 2 (Fin 2 → ℝ) z) 1)
    (Icc ((WithLp.equiv 2 (Fin 2 → ℝ) z) 0-W/4)
      ((WithLp.equiv 2 (Fin 2 → ℝ) z) 0+W/4)) (W/4)

theorem constantPlanarStripPoint_dist_center (z : WithLp 2 (Fin 2 → ℝ)) (q : ℝ) :
    dist (signedPlanarStripPoint 0 1 (fun _ => (WithLp.equiv 2 (Fin 2 → ℝ) z) 1) q 0) z =
      |q-(WithLp.equiv 2 (Fin 2 → ℝ) z) 0| := by
  rw [PiLp.dist_eq_of_L2, Fin.sum_univ_two]
  simp [signedPlanarStripPoint,signedPlanarDecode,Real.dist_eq,Real.sqrt_sq_eq_abs]

theorem bufferedPointRectangle_subset_closedBall (z : WithLp 2 (Fin 2 → ℝ)) (W : ℝ) :
    bufferedPointRectangle z W ⊆ Metric.closedBall z (W/2) := by
  rintro p ⟨q,hq,u,hu,rfl⟩
  have hqabs : |q-(WithLp.equiv 2 (Fin 2 → ℝ) z) 0| ≤ W/4 :=
    abs_le.mpr ⟨by linarith [hq.1], by linarith [hq.2]⟩
  calc
    dist _ z ≤ dist _ (signedPlanarStripPoint 0 1
        (fun _ => (WithLp.equiv 2 (Fin 2 → ℝ) z) 1) q 0) +
        dist (signedPlanarStripPoint 0 1 (fun _ => (WithLp.equiv 2 (Fin 2 → ℝ) z) 1) q 0) z :=
      dist_triangle _ _ _
    _ = |u|+|q-(WithLp.equiv 2 (Fin 2 → ℝ) z) 0| := by
      rw [signedPlanarStripPoint_dist,constantPlanarStripPoint_dist_center]
    _ ≤ W/2 := by linarith

theorem bufferedPointRectangle_subset_of_band
    {E : Set (WithLp 2 (Fin 2 → ℝ))} {W : ℝ} {z : WithLp 2 (Fin 2 → ℝ)}
    (hz : z ∈ bufferedDistanceBand E W) : bufferedPointRectangle z W ⊆ E := by
  intro p hp
  apply Metric.ball_infDist_compl_subset (s := E)
  exact (bufferedPointRectangle_subset_closedBall z W hp).trans_lt hz.1

theorem bufferedPointRectangle_measurable_volume
    (z : WithLp 2 (Fin 2 → ℝ)) {W : ℝ} (hW : 0 ≤ W) :
    MeasurableSet (bufferedPointRectangle z W) ∧
      volume.real (bufferedPointRectangle z W) = W*W/4 := by
  refine ⟨(signedPlanarStrip_measurable_volume 0 1 (Or.inl rfl) _ _ _ _
    continuousOn_const).1,?_⟩
  unfold bufferedPointRectangle
  rw [volume_real_signedPlanarStrip_quarter 0 1 (Or.inl rfl) _ _ _ _
    continuousOn_const (by linarith) hW]
  ring

theorem constant_centerline_all_order_prepared (c : ℝ) :
    AnalyticOnNhd ℝ (fun _ : ℝ => c) univ ∧
    (∀ (n : ℕ) (x : ℝ), iteratedDeriv n (fun _ : ℝ => c-c) x = 0) ∧
    (∀ (n : ℕ), 0 < n → ∀ x : ℝ, iteratedDeriv n (fun _ : ℝ => c) x = 0) := by
  have hzero : ∀ n : ℕ, iteratedDeriv n (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n hn => rw [iteratedDeriv_succ,hn]; funext x; exact deriv_const x 0
  refine ⟨analyticOnNhd_const,?_,?_⟩
  · intro n x
    simpa only [sub_self] using congrFun (hzero n) x
  · intro n hn x
    cases n with
    | zero => omega
    | succ n =>
      have hc : deriv (fun _ : ℝ => c) = fun _ => 0 := funext (fun x => deriv_const x c)
      rw [iteratedDeriv_succ',hc,hzero]

theorem bufferedBandComponent_small_strip
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (hE : Bornology.IsBounded E)
    {W : ℝ} (hW : 0 < W) {z : WithLp 2 (Fin 2 → ℝ)}
    (hz : z ∈ bufferedDistanceBand E W)
    (hsmall : Metric.diam (bufferedBandComponent E W z) ≤ W) :
    bufferedComponentScale E W z = W ∧
    bufferedBandComponent E W z ⊆ Metric.closedBall z (bufferedComponentScale E W z) ∧
    bufferedPointRectangle z W ⊆ E ∧
    bufferedPointRectangle z W ⊆ Metric.closedBall z (W/2) ∧
    MeasurableSet (bufferedPointRectangle z W) ∧
    volume.real (bufferedPointRectangle z W) = bufferedComponentScale E W z*W/4 := by
  have hscale : bufferedComponentScale E W z = W := max_eq_left hsmall
  have harea := bufferedPointRectangle_measurable_volume z hW.le
  exact ⟨hscale,bufferedBandComponent_subset_closedBall hE hW.le (mem_bufferedBandComponent hz),
    bufferedPointRectangle_subset_of_band hz,bufferedPointRectangle_subset_closedBall z W,
    harea.1,by simpa only [hscale] using harea.2⟩

end PaperI
