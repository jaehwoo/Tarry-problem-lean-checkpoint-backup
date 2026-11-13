import PaperILean.BoundedCharacteristicVariational

open Set Filter Metric MeasureTheory
open scoped Topology NNReal

noncomputable section

namespace PaperI.BoundedCharacteristic

private def clip (r x : ℝ) : ℝ := max (-r) (min r x)

private theorem clip_mem {r : ℝ} (hr : 0 ≤ r) (x : ℝ) : clip r x ∈ Icc (-r) r := by
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

private theorem clip_eq {r x : ℝ} (hx : x ∈ Icc (-r) r) : clip r x = x := by
  simp [clip, min_eq_right hx.2, max_eq_right hx.1]

private theorem clip_lipschitz (r : ℝ) : LipschitzWith 1 (clip r) := by
  simpa [clip, id] using
    (LipschitzWith.const (α := ℝ) (-r)).max
      ((LipschitzWith.const (α := ℝ) r).min LipschitzWith.id)

private theorem tube_mem_cthickening {T r z : ℝ} {y : ℝ → ℝ} {t x : ℝ}
    (ht : t ∈ window T) (hx : |x| ≤ r) :
    (y t+x,z+t) ∈ cthickening r (point y z '' window T) := by
  apply mem_cthickening_of_dist_le _ (point y z t) r _
    (mem_image_of_mem _ ht)
  have he : (y t+x) - y t = x := by ring
  rw [Prod.dist_eq]
  change max (dist (y t+x) (y t)) (dist (z+t) (z+t)) ≤ r
  rw [dist_self, Real.dist_eq, he, max_eq_left (abs_nonneg x)]
  exact hx

private theorem signed_integral_bound {T L : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hf : ∀ t ∈ window T, |f t| ≤ L) {t : ℝ} (ht : t ∈ window T) :
    |∫ s in (0:ℝ)..t, f s| ≤ L * |t| := by
  have hz : 0 ∈ window T := ⟨neg_nonpos.mpr hT,hT⟩
  have hb : ∀ s ∈ uIoc (0 : ℝ) t, ‖f s‖ ≤ L := by
    intro s hs
    rw [Real.norm_eq_abs]
    exact hf s (uIcc_subset_Icc hz ht (uIoc_subset_uIcc hs))
  simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const hb

private theorem exists_nearby_deviation {T L r z h : ℝ}
    (hT : 0 < T) (hL : 0 ≤ L) (hr : 0 < r)
    (hsmall : L*T ≤ Real.log 2) (hh : |h| < (1-L*T)*r)
    {D : Set Plane} {d u : Plane → ℝ} {y : ℝ → ℝ}
    (hd : ContinuousOn d D) (hy : ContinuousOn y (window T))
    (hdu : ∀ p ∈ D, HasDerivAt (fun x => d (x,p.2)) (u p) p.1)
    (hbound : ∀ p ∈ D, |u p| ≤ L)
    (htube : cthickening r (point y z '' window T) ⊆ D) :
    ∃ w : ℝ → ℝ, w 0 = h ∧
      (∀ t ∈ window T, |w t| < r) ∧
      (∀ t ∈ window T,
        HasDerivWithinAt w (d (y t+w t,z+t)-d (y t,z+t)) (window T) t) := by
  let K : ℝ≥0 := ⟨L,hL⟩
  let v := fun t x => d (y t+clip r x,z+t)-d (y t,z+t)
  have hmem : ∀ t ∈ window T, ∀ x ∈ Icc (-r) r, (y t+x,z+t) ∈ D := by
    intro t ht x hx
    exact htube (tube_mem_cthickening ht (abs_le.mpr hx))
  have hlip : ∀ t ∈ window T, LipschitzOnWith K (fun x => d (y t+x,z+t)) (Icc (-r) r) := by
    intro t ht
    have hder : ∀ x ∈ Icc (-r) r,
        HasDerivAt (fun x => d (y t+x,z+t)) (u (y t+x,z+t)) x := by
      intro x hx
      simpa [Function.comp_def] using
        (hdu _ (hmem t ht x hx)).scomp x ((hasDerivAt_id x).const_add (y t))
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun x hx => (hder x hx).differentiableAt)
      _ (convex_Icc _ _)
    intro x hx
    rw [(hder x hx).deriv]
    exact_mod_cast (show ‖u (y t+x,z+t)‖ ≤ L from by
      rw [Real.norm_eq_abs]
      exact hbound _ (hmem t ht x hx))
  have hzero : (0:ℝ) ∈ Icc (-r) r := ⟨by linarith,hr.le⟩
  have hvL : ∀ t ∈ window T, LipschitzWith K (v t) := by
    intro t ht
    apply LipschitzWith.of_dist_le_mul
    intro x x'
    have he : dist (v t x) (v t x') =
        dist (d (y t+clip r x,z+t)) (d (y t+clip r x',z+t)) := by
      dsimp [v]
      rw [dist_sub_right]
    rw [he]
    exact ((hlip t ht).dist_le_mul _ (clip_mem hr.le _) _ (clip_mem hr.le _)).trans
      (mul_le_mul_of_nonneg_left
        (by simpa using (clip_lipschitz r).dist_le_mul x x') K.coe_nonneg)
  have hvC : ∀ t ∈ window T, ∀ x : ℝ, ‖v t x‖ ≤ L*r := by
    intro t ht x
    have hh := (hlip t ht).dist_le_mul _ (clip_mem hr.le x) 0 hzero
    have hclip : |clip r x| ≤ r := abs_le.mpr (clip_mem hr.le x)
    have hb : dist (clip r x) 0 ≤ r := by simpa [Real.dist_eq] using hclip
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hb K.coe_nonneg)
    simpa [v, Real.dist_eq, Real.norm_eq_abs, K] using hh'
  have hv_cont : ∀ x : ℝ, ContinuousOn (fun t => v t x) (window T) := by
    intro x
    have h1 : ContinuousOn (fun t => d (y t+clip r x,z+t)) (window T) :=
      hd.comp ((hy.add continuousOn_const).prodMk (by fun_prop))
        (fun t ht => hmem t ht _ (clip_mem hr.le _))
    have h2 : ContinuousOn (fun t => d (y t,z+t)) (window T) :=
      hd.comp (hy.prodMk (by fun_prop)) (fun t ht => by
        simpa using hmem t ht 0 hzero)
    exact h1.sub h2
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ) ≠ 1)
    linarith
  have hz : (0:ℝ) ∈ window T := ⟨by linarith,hT.le⟩
  have hC : (L*r) * max (T-0) (0-(-T)) ≤ r := by
    rw [sub_zero, zero_sub, neg_neg, max_self]
    have hb : L*T ≤ 1 := hsmall.trans hlog.le
    calc L*r*T = (L*T)*r := by ring
         _ ≤ 1*r := mul_le_mul_of_nonneg_right hb hr.le
         _ = r := one_mul _
  have hpl : IsPicardLindelof v (-T) 0 T h K r (L*r) :=
    ⟨hz,hr.le,fun t ht => (hvL t ht).lipschitzOnWith,
      fun x _ => hv_cont x,fun t ht x _ => hvC t ht x,hC⟩
  obtain ⟨w,hw0,hw⟩ := hpl.exists_forall_hasDerivWithinAt_Icc_eq h
  have hdb : ∀ t ∈ window T, ‖derivWithin w (window T) t‖ ≤ L*r := by
    intro t ht
    change ‖derivWithin w (Icc (-T) T) t‖ ≤ L*r
    rw [(hw t ht).derivWithin (uniqueDiffOn_Icc (by linarith : -T<T) t ht)]
    exact hvC t ht _
  have hwLt : ∀ t ∈ window T, |w t| < r := by
    intro t ht
    have hm := Convex.norm_image_sub_le_of_norm_derivWithin_le
      (fun s hs => (hw s hs).differentiableWithinAt) hdb (convex_Icc (-T) T)
      (show 0 ∈ window T from ⟨by linarith,hT.le⟩) ht
    rw [hw0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hm
    have hb := mul_le_mul_of_nonneg_left (abs_le.mpr ht) (mul_nonneg hL hr.le)
    calc
      |w t| = |w t-h+h| := by ring_nf
      _ ≤ |w t-h|+|h| := abs_add _ _
      _ ≤ (L*r)*|t|+|h| := add_le_add_right hm _
      _ ≤ (L*r)*T+|h| := add_le_add_right hb _
      _ < r := by nlinarith
  refine ⟨w,hw0,hwLt,?_⟩
  intro t ht
  have he := clip_eq ((abs_le.mp (hwLt t ht).le))
  simpa [v, he] using hw t ht

private theorem deviation_controls {T L r z h : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hsmall : L*T ≤ Real.log 2)
    {D : Set Plane} {d u : Plane → ℝ} {y w : ℝ → ℝ}
    (hy : ContinuousOn y (window T)) (hu : ContinuousOn u D)
    (hdu : ∀ p ∈ D, HasDerivAt (fun x => d (x,p.2)) (u p) p.1)
    (hbound : ∀ p ∈ D, |u p| ≤ L)
    (htube : cthickening r (point y z '' window T) ⊆ D)
    (hw0 : w 0 = h) (hwLt : ∀ t ∈ window T, |w t| < r)
    (hw : ∀ t ∈ window T,
      HasDerivWithinAt w (d (y t+w t,z+t)-d (y t,z+t)) (window T) t) :
    ContinuousOn (differenceCoefficient u y w z) (window T) ∧
      (∀ t ∈ window T,
        w t = h * Real.exp (∫ s in (0:ℝ)..t, differenceCoefficient u y w z s)) ∧
      (∀ t ∈ window T, |w t| ≤ 2*|h|) := by
  let A := differenceCoefficient u y w z
  have hmem : ∀ t ∈ window T, ∀ q ∈ Icc (0:ℝ) 1,
      (y t+q*w t,z+t) ∈ D := by
    intro t ht q hq
    apply htube
    apply tube_mem_cthickening ht
    rw [abs_mul, abs_of_nonneg hq.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) hq.2).trans (hwLt t ht).le
  have hc : ContinuousOn A (window T) :=
    differenceCoefficient_continuousOn hu hy
      (fun t ht => (hw t ht).continuousWithinAt) hmem
  have he : ∀ t ∈ window T, w t = h * Real.exp (∫ s in (0:ℝ)..t, A s) := by
    intro t ht
    have hlin : ∀ s ∈ window T, HasDerivWithinAt w (A s * w s) (window T) s := by
      intro s hs
      convert hw s hs using 1
      exact (horizontal_difference hu hdu (hmem s hs)).symm
    rw [← hw0]
    exact exponential_solution_window hT hc hlin ht
  have hAb : ∀ t ∈ window T, |A t| ≤ L := by
    intro t ht
    have hnorm : ∀ q ∈ uIoc (0:ℝ) 1, ‖u (y t+q*w t,z+t)‖ ≤ L := by
      intro q hq
      have hq' := uIoc_subset_uIcc hq
      rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hq'
      rw [Real.norm_eq_abs]
      exact hbound _ (hmem t ht q hq')
    change |∫ q in (0:ℝ)..1, u (y t+q*w t,z+t)| ≤ L
    simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const hnorm
  refine ⟨hc,he,fun t ht => ?_⟩
  rw [he t ht, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h := (exponential_bounds hT hL hsmall hAb ht).2.1
  exact (mul_le_mul_of_nonneg_left h (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- Near the given initial value, the actual neighbouring characteristics exist
and their transverse derivative at the original characteristic is the
oriented exponential integral. The auxiliary clip is absent from the result. -/
theorem actual_transverse_derivative {T L z : ℝ}
    (hT : 0 < T) (hL : 0 ≤ L) (hsmall : L*T ≤ Real.log 2)
    {D : Set Plane} (hD : IsOpen D) {d u : Plane → ℝ} {y : ℝ → ℝ}
    (hd : ContinuousOn d D) (hu : ContinuousOn u D)
    (hdu : ∀ p ∈ D, HasDerivAt (fun x => d (x,p.2)) (u p) p.1)
    (hbound : ∀ p ∈ D, |u p| ≤ L)
    (hyD : ∀ t ∈ window T, point y z t ∈ D)
    (hy : ∀ t ∈ window T, HasDerivWithinAt y (d (point y z t)) (window T) t) :
    ∃ F : ℝ → ℝ → ℝ, ∃ ρ > 0, F (y 0) = y ∧
      (∀ x, |x-y 0|<ρ → F x 0=x ∧
        (∀ t ∈ window T, point (F x) z t ∈ D ∧
          HasDerivWithinAt (F x) (d (point (F x) z t)) (window T) t)) ∧
      ∀ t ∈ window T,
        HasDerivAt (fun x => F x t) (Real.exp (∫ s in (0:ℝ)..t, u (point y z s))) (y 0) := by
  have hyc : ContinuousOn y (window T) := fun t ht => (hy t ht).continuousWithinAt
  have hpc : ContinuousOn (point y z) (window T) := hyc.prodMk (by fun_prop)
  have hK : IsCompact (point y z '' window T) := isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨r,hr,htube⟩ := hK.exists_cthickening_subset_open hD
    (by rintro _ ⟨t,ht,rfl⟩; exact hyD t ht)
  let ρ := (1-L*T)*r
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ) ≠ 1)
    linarith
  have hρ : 0 < ρ := mul_pos (sub_pos.mpr (hsmall.trans_lt hlog)) hr
  have hselect : ∀ h : ℝ, ∃ w : ℝ → ℝ,
      |h| < ρ → w 0 = h ∧ (∀ t ∈ window T, |w t| < r) ∧
        ∀ t ∈ window T,
          HasDerivWithinAt w (d (y t+w t,z+t)-d (y t,z+t)) (window T) t := by
    intro h
    by_cases hh : |h| < ρ
    · obtain ⟨w,hw⟩ := exists_nearby_deviation hT hL hr hsmall hh hd hyc hdu hbound htube
      exact ⟨w,fun _ => hw⟩
    · exact ⟨fun _ => 0,fun h' => False.elim (hh h')⟩
  choose chosen hchosen using hselect
  let w := fun h => if h = 0 then fun _ => 0 else chosen h
  have hw : ∀ h : ℝ, |h| < ρ → w h 0 = h ∧ (∀ t ∈ window T, |w h t| < r) ∧
        ∀ t ∈ window T,
          HasDerivWithinAt (w h) (d (y t+w h t,z+t)-d (y t,z+t)) (window T) t := by
    intro h hh
    by_cases h0 : h = 0
    · subst h
      simp only [w, if_pos rfl, add_zero, sub_self, abs_zero]
      exact ⟨trivial,fun _ _ => hr,fun _ _ => (hasDerivAt_const _ _).hasDerivWithinAt⟩
    · simpa [w,h0] using hchosen h hh
  let F := fun x t => y t+w (x-y 0) t
  have hF0 : F (y 0) = y := by
    funext t
    simp [F,w]
  refine ⟨F,ρ,hρ,hF0,?_,?_⟩
  · intro x hx
    obtain ⟨hw0,hwLt,hder⟩ := hw (x-y 0) hx
    refine ⟨?_,fun t ht => ⟨htube (tube_mem_cthickening ht (hwLt t ht).le),?_⟩⟩
    · dsimp [F]
      rw [hw0]
      ring
    · have he := (hy t ht).add (hder t ht)
      convert he using 1
      simp [point,F]
  · intro t ht
    rw [hasDerivAt_iff_tendsto_slope_zero]
    let A := fun h => differenceCoefficient u y (w h) z
    let B := fun s => u (point y z s)
    have hcB : ContinuousOn B (window T) := hu.comp hpc hyD
    have hcontrols : ∀ h : ℝ, |h| < ρ →
        ContinuousOn (A h) (window T) ∧
        (∀ s ∈ window T, w h s = h * Real.exp (∫ q in (0:ℝ)..s, A h q)) ∧
        (∀ s ∈ window T, |w h s| ≤ 2*|h|) := by
      intro h hh
      obtain ⟨hw0,hwLt,hder⟩ := hw h hh
      exact deviation_controls hT.le hL hsmall hyc hu hdu hbound htube hw0 hwLt hder
    have hUC := Metric.uniformContinuousOn_iff.mp
      (hK.cthickening.uniformContinuousOn_of_continuous (hu.mono htube))
    have hunif : ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, |h| < δ →
        |h| < ρ ∧ ∀ s ∈ window T, |A h s - B s| ≤ ε := by
      intro ε hε
      obtain ⟨δ,hδ,hmod⟩ := hUC ε hε
      refine ⟨min ρ (δ/2),lt_min hρ (by positivity),fun h hh => ?_⟩
      have hρh := lt_of_lt_of_le hh (min_le_left _ _)
      refine ⟨hρh,fun s hs => ?_⟩
      have hb : ∀ q ∈ uIoc (0:ℝ) 1,
          ‖u (y s+q*w h s,z+s)-B s‖ ≤ ε := by
        intro q hq
        have hq' := uIoc_subset_uIcc hq
        rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hq'
        have hrel : |q*w h s| ≤ |w h s| := by
          rw [abs_mul,abs_of_nonneg hq'.1]
          exact mul_le_of_le_one_left (abs_nonneg _) hq'.2
        have hwp := hrel.trans ((hw h hρh).2.1 s hs).le
        have hdist : dist (y s+q*w h s,z+s) (point y z s) < δ := by
          have he : y s+q*w h s-y s = q*w h s := by ring
          rw [Prod.dist_eq]
          change max (dist (y s+q*w h s) (y s)) (dist (z+s) (z+s)) < δ
          rw [dist_self,Real.dist_eq,he,max_eq_left (abs_nonneg _)]
          have hg := (hcontrols h hρh).2.2 s hs
          have hm := lt_of_lt_of_le hh (min_le_right ρ (δ/2))
          linarith
        have hbase := tube_mem_cthickening (y:=y) (z:=z) hs (show |(0:ℝ)| ≤ r by simpa using hr.le)
        have he := hmod _ (tube_mem_cthickening hs hwp) _ (by simpa [point] using hbase) hdist
        simpa [Real.dist_eq,Real.norm_eq_abs,B] using he.le
      have hsfun : ContinuousOn (fun q : ℝ => u (y s+q*w h s,z+s)) (uIcc (0:ℝ) 1) := by
        rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)]
        apply hu.comp (by fun_prop)
        intro q hq
        apply htube
        apply tube_mem_cthickening hs
        rw [abs_mul,abs_of_nonneg hq.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) hq.2).trans ((hw h hρh).2.1 s hs).le
      have hsub := intervalIntegral.integral_sub hsfun.intervalIntegrable
        ((continuous_const : Continuous (fun _ : ℝ => B s)).intervalIntegrable (μ:=volume) 0 1)
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hb
      rw [hsub] at hnorm
      simpa [A,differenceCoefficient,Real.norm_eq_abs] using hnorm
    have hlim : Tendsto (fun h => ∫ s in (0:ℝ)..t, A h s) (𝓝 (0:ℝ))
        (𝓝 (∫ s in (0:ℝ)..t, B s)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      let η := ε / (T+1)
      have hη : 0 < η := div_pos hε (by linarith)
      obtain ⟨δ,hδ,hunif'⟩ := hunif η hη
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) hδ] with h hh
      have hh' : |h| < δ := by simpa [Metric.mem_ball,Real.dist_eq] using hh
      obtain ⟨hρh,hb⟩ := hunif' h hh'
      have hz : (0:ℝ) ∈ window T := ⟨by linarith,hT.le⟩
      have hsub := intervalIntegral.integral_sub
        (((hcontrols h hρh).1.mono (uIcc_subset_Icc hz ht)).intervalIntegrable (μ:=volume))
        ((hcB.mono (uIcc_subset_Icc hz ht)).intervalIntegrable (μ:=volume))
      have hnorm := signed_integral_bound hT.le hb ht
      rw [hsub] at hnorm
      rw [Real.dist_eq]
      refine hnorm.trans_lt ?_
      have ht' := abs_le.mpr ht
      calc
        η*|t| ≤ η*T := mul_le_mul_of_nonneg_left ht' hη.le
        _ < η*(T+1) := mul_lt_mul_of_pos_left (by linarith) hη
        _ = ε := div_mul_cancel₀ _ (by linarith)
    have hexp : Tendsto (fun h => Real.exp (∫ s in (0:ℝ)..t, A h s)) (𝓝[≠] (0:ℝ))
        (𝓝 (Real.exp (∫ s in (0:ℝ)..t, B s))) :=
      Real.continuous_exp.continuousAt.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds hlim)
    apply hexp.congr'
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℝ) hρ)]
      with h h0 hh
    have h0' : h ≠ 0 := h0
    have hh' : |h| < ρ := by simpa [Metric.mem_ball,Real.dist_eq] using hh
    have hrel : (y 0+h)-y 0=h := by ring
    have he : w h t = h*Real.exp (∫ s in (0:ℝ)..t, A h s) := (hcontrols h hh').2.1 t ht
    rw [hF0]
    change Real.exp (∫ s in (0:ℝ)..t, A h s) =
      h⁻¹ * (y t+w ((y 0+h)-y 0) t-y t)
    rw [hrel,he]
    field_simp

end PaperI.BoundedCharacteristic
