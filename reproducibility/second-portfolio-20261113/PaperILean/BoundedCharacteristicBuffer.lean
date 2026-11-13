import PaperILean.BoundedCharacteristicContinuation

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace PaperI.BoundedCharacteristic

/-- Metric absolute continuity on a compact interval, in its equivalent
integrable-majorant form. All absolutely continuous planar paths are allowed. -/
def ACPath (γ : ℝ → Plane) (T : ℝ) : Prop :=
  ∃ majorant : ℝ → ℝ, IntervalIntegrable majorant volume 0 T ∧
    (∀ r, 0≤majorant r) ∧
    ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s≤t →
      dist (γ s) (γ t) ≤ ∫ r in s..t, majorant r

/-- Extended first-exit length. Infinite-length AC paths are allowed. -/
def acLength (d : Plane → ℝ) (γ : ℝ → Plane) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc (0:ℝ) T, ENNReal.ofReal (coframeSpeed d γ t)

def ACFirstExit (D : Set Plane) (p : Plane) (T : ℝ) (γ : ℝ → Plane) : Prop :=
  0 ≤ T ∧ γ 0 = p ∧ ACPath γ T ∧
    (∀ t ∈ Ico 0 T, γ t ∈ D) ∧ γ T ∉ D

def HasACBuffer (D : Set Plane) (d : Plane → ℝ) (p : Plane) (M : ℝ) : Prop :=
  ∀ T γ, ACFirstExit D p T γ → ENNReal.ofReal M ≤ acLength d γ T

private theorem ae_ne_at (b : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
  rw [ae_iff]
  simp

theorem lipschitz_acPath {γ : ℝ → Plane} {T : ℝ} (hγ : LipschitzPath γ T) :
    ACPath γ T := by
  obtain ⟨K,hK⟩ := hγ
  refine ⟨fun _ => K,continuous_const.intervalIntegrable _ _,fun _ => K.coe_nonneg,?_⟩
  intro s hs t ht hst
  rw [intervalIntegral.integral_const]
  have h := hK.dist_le_mul s hs t ht
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hst)] at h
  simpa [smul_eq_mul,mul_comm] using h

private theorem directed_acLength {d : Plane → ℝ} {z σ T : ℝ} {y : ℝ → ℝ}
    (hT : 0≤T) (hσ : |σ|=1)
    (hy : ∀ t ∈ Ioo (0:ℝ) T, HasDerivAt y (σ*d (directedPoint z σ y t)) t) :
    acLength d (directedPoint z σ y) T=ENNReal.ofReal T := by
  have h := directed_length_of_interior hT hσ hy
  have hi : Integrable (coframeSpeed d (directedPoint z σ y)) (volume.restrict (Ioc 0 T)) := by
    simpa [uIoc_of_le hT] using intervalIntegrable_iff.mp h.1
  have hn : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] coframeSpeed d (directedPoint z σ y) :=
    Filter.Eventually.of_forall (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  have he := ofReal_integral_eq_lintegral_ofReal hi hn
  rw [coframeLength,intervalIntegral.integral_of_le hT] at h
  exact he.symm.trans (congrArg ENNReal.ofReal h.2)

theorem source_buffer_implies_lipschitz_first_exit
    {D : Set Plane} {d : Plane → ℝ} {p : Plane} {M : ℝ}
    (h : HasACBuffer D d p M) {T : ℝ} {γ : ℝ → Plane}
    (hT : 0≤T) (hγ0 : γ 0=p) (hγAC : ACPath γ T)
    (hγD : ∀ t ∈ Ico 0 T, γ t∈D) (hExit : γ T∉D)
    (hFin : IntervalIntegrable (coframeSpeed d γ) volume 0 T) :
    ENNReal.ofReal M ≤ ENNReal.ofReal (coframeLength d γ T) := by
  have hi : Integrable (coframeSpeed d γ) (volume.restrict (Ioc 0 T)) := by
    simpa [uIoc_of_le hT] using intervalIntegrable_iff.mp hFin
  have hn : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] coframeSpeed d γ :=
    Filter.Eventually.of_forall (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  have he := ofReal_integral_eq_lintegral_ofReal hi hn
  rw [←intervalIntegral.integral_of_le hT] at he
  exact (h T γ ⟨hT,hγ0,hγAC,hγD,hExit⟩).trans_eq he.symm

/-- Exact source initial buffer supports the directed continuation theorem. -/
theorem source_directed_continuation {D : Set Plane} (hD : IsOpen D) {d v : Plane → ℝ}
    (hd : ∀ p ∈ D, ContDiffAt ℝ 1 d p)
    (hv : ∀ p ∈ D, fderiv ℝ d p (d p,1)=v p)
    {V z σ H y₀ M : ℝ} (hV : ∀ p ∈ D, |v p|≤V) (hσ : |σ|=1)
    (hH : 0<H) (hMH : H<M) (hp : (y₀,z) ∈ D)
    (hbuffer : HasACBuffer D d (y₀,z) M) :
    ∃ y : ℝ → ℝ, y 0=y₀ ∧ DirectedSolution D d z σ 0 H y := by
  apply directed_continuation_with_exit_control hD hd hv hV hσ hH hMH hp
  intro b y hExit hder
  have hM := source_buffer_implies_lipschitz_first_exit hbuffer hExit.1 hExit.2.1
    (lipschitz_acPath hExit.2.2.1) hExit.2.2.2.2.1 hExit.2.2.2.2.2 hExit.2.2.2.1
  have hl := (directed_length_of_interior hExit.1 hσ hder).2
  rw [hl] at hM ⊢
  exact (ENNReal.ofReal_le_ofReal_iff hExit.1).mp hM

private def prepend (b : ℝ) (γ η : ℝ → Plane) (t : ℝ) : Plane :=
  if t≤b then γ t else η (t-b)

private theorem prepend_eq_right {b : ℝ} {γ η : ℝ → Plane} (h : γ b=η 0)
    {t : ℝ} (ht : b≤t) : prepend b γ η t=η (t-b) := by
  rcases lt_or_eq_of_le ht with hlt | rfl
  · simp [prepend,not_le_of_gt hlt]
  · simpa [prepend] using h

private theorem join_integrable {b c : ℝ} (hb : 0≤b) (hc : 0≤c)
    {g f : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 b)
    (hf : IntervalIntegrable f volume 0 c) :
    let p := fun t => if t≤b then g t else f (t-b)
    IntervalIntegrable p volume 0 b ∧ IntervalIntegrable p volume b (b+c) := by
  dsimp only
  have h₁ : ∀ᵐ t ∂(volume.restrict (uIoc (0:ℝ) b)),
      g t = if t≤b then g t else f (t-b) := by
    filter_upwards [ae_restrict_mem (s:=uIoc (0:ℝ) b) measurableSet_uIoc] with t ht
    rw [uIoc_of_le hb] at ht
    simp [ht.2]
  have h₂ : ∀ᵐ t ∂(volume.restrict (uIoc b (b+c))),
      f (t-b) = if t≤b then g t else f (t-b) := by
    filter_upwards [ae_restrict_mem (s:=uIoc b (b+c)) measurableSet_uIoc] with t ht
    rw [uIoc_of_le (by linarith : b≤b+c)] at ht
    simp [not_le_of_gt ht.1]
  exact ⟨hg.congr h₁,(by simpa [add_comm] using hf.comp_sub_right b :
    IntervalIntegrable (fun t => f (t-b)) volume b (b+c)).congr h₂⟩

private theorem integral_join_left {b s t : ℝ} {g f : ℝ → ℝ}
    (hst : s≤t) (ht : t≤b) :
    (∫ r in s..t, (if r≤b then g r else f (r-b))) = ∫ r in s..t, g r := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hst] at hr
  simp [hr.2.trans ht]

private theorem integral_join_right {b s t : ℝ} {g f : ℝ → ℝ}
    (hbs : b≤s) (hst : s≤t) :
    (∫ r in s..t, (if r≤b then g r else f (r-b))) = ∫ r in s-b..t-b, f r := by
  rw [←intervalIntegral.integral_comp_sub_right]
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall fun r hr => by
    rw [uIoc_of_le hst] at hr
    simp [not_le_of_gt (hbs.trans_lt hr.1)]

private theorem prepend_ac {b c : ℝ} (hb : 0≤b) (hc : 0≤c)
    {γ η : ℝ → Plane} (hγ : ACPath γ b) (hη : ACPath η c) (hjoin : γ b=η 0) :
    ACPath (prepend b γ η) (b+c) := by
  obtain ⟨g,hgI,hg0,hγ⟩ := hγ
  obtain ⟨f,hfI,hf0,hη⟩ := hη
  let p := fun t => if t≤b then g t else f (t-b)
  obtain ⟨h₁,h₂⟩ := join_integrable hb hc hgI hfI
  refine ⟨p,h₁.trans h₂,fun t => by by_cases h : t≤b <;> simp [p,h,hg0,hf0],?_⟩
  intro s hs t ht hst
  by_cases htl : t≤b
  · change dist (prepend b γ η s) (prepend b γ η t) ≤ ∫ r in s..t, p r
    rw [show prepend b γ η s=γ s by simp [prepend,hst.trans htl],
      show prepend b γ η t=γ t by simp [prepend,htl]]
    rw [show (∫ r in s..t, p r)=∫ r in s..t, g r from integral_join_left (f:=f) hst htl]
    exact hγ s ⟨hs.1,hst.trans htl⟩ t ⟨ht.1,htl⟩ hst
  by_cases hsr : b≤s
  · rw [prepend_eq_right hjoin hsr,prepend_eq_right hjoin (hsr.trans hst)]
    rw [show (∫ r in s..t, p r)=∫ r in s-b..t-b, f r from integral_join_right (g:=g) hsr hst]
    exact hη (s-b) ⟨sub_nonneg.mpr hsr,by linarith [hs.2]⟩
      (t-b) ⟨sub_nonneg.mpr (hsr.trans hst),by linarith [ht.2]⟩ (sub_le_sub_right hst _)
  have hsb : s≤b := (lt_of_not_ge hsr).le
  have hbt : b≤t := (lt_of_not_ge htl).le
  have hi₁ : IntervalIntegrable p volume s b :=
    h₁.mono_set (uIcc_subset_Icc ⟨hs.1,hsb⟩ ⟨hb,le_rfl⟩ |>.trans (by rw [uIcc_of_le hb]))
  have hi₂ : IntervalIntegrable p volume b t :=
    h₂.mono_set (uIcc_subset_Icc ⟨le_rfl,by linarith⟩ ⟨hbt,ht.2⟩ |>.trans
      (by rw [uIcc_of_le (by linarith : b≤b+c)]))
  have hγ' := hγ s ⟨hs.1,hsb⟩ b ⟨hb,le_rfl⟩ hsb
  have hη' := hη 0 ⟨le_rfl,hc⟩ (t-b) ⟨sub_nonneg.mpr hbt,by linarith [ht.2]⟩ (sub_nonneg.mpr hbt)
  calc
    dist (prepend b γ η s) (prepend b γ η t)
        ≤ dist (prepend b γ η s) (γ b) + dist (γ b) (prepend b γ η t) := dist_triangle _ _ _
    _ ≤ (∫ r in s..b, g r) + ∫ r in (0:ℝ)..t-b, f r := by
      rw [show prepend b γ η s=γ s by simp [prepend,hsb],prepend_eq_right hjoin hbt,hjoin]
      exact add_le_add (hjoin ▸ hγ') hη'
    _ = (∫ r in s..b, p r) + ∫ r in b..t, p r := by
      rw [show (∫ r in s..b, p r)=∫ r in s..b, g r from integral_join_left (f:=f) hsb le_rfl,
        show (∫ r in b..t, p r)=∫ r in b-b..t-b, f r from integral_join_right (g:=g) le_rfl hbt,
        sub_self]
    _ = ∫ r in s..t, p r := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂

private theorem translate_length {b c : ℝ} (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc b (b+c), f (t-b)) = ∫⁻ t in Ioc (0:ℝ) c, f t := by
  have hm : MeasurePreserving (fun t : ℝ => t-b) volume volume := by
    simpa [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-b)
  have hme : MeasurableEmbedding (fun t : ℝ => t-b) :=
    by simpa [sub_eq_add_neg] using (Homeomorph.addRight (-b)).isClosedEmbedding.measurableEmbedding
  have hp : (fun t : ℝ => t-b) ⁻¹' Ioc 0 c = Ioc b (b+c) := by
    ext t
    change (0<t-b ∧ t-b≤c) ↔ b<t ∧ t≤b+c
    constructor <;> rintro ⟨h₁,h₂⟩ <;> exact ⟨by linarith,by linarith⟩
  have hr := hm.restrict_preimage (s:=Ioc 0 c) measurableSet_Ioc
  rw [hp] at hr
  exact hr.lintegral_comp_emb hme f

private theorem prepend_length {b c : ℝ} (hb : 0≤b) (hc : 0≤c)
    {d : Plane → ℝ} {γ η : ℝ → Plane} :
    acLength d (prepend b γ η) (b+c)=acLength d γ b+acLength d η c := by
  let F := fun t => ENNReal.ofReal (coframeSpeed d (prepend b γ η) t)
  have hdis : Disjoint (Ioc (0:ℝ) b) (Ioc b (b+c)) :=
    disjoint_left.mpr fun _ h₁ h₂ => (not_lt_of_ge h₁.2) h₂.1
  have hleft : ∀ᵐ t ∂(volume.restrict (Ioc (0:ℝ) b)),
      F t = ENNReal.ofReal (coframeSpeed d γ t) := by
    filter_upwards [ae_restrict_mem (s:=Ioc (0:ℝ) b) measurableSet_Ioc,
      (ae_ne_at b).filter_mono (ae_mono Measure.restrict_le_self)] with t ht hne
    have hlt : t<b := lt_of_le_of_ne ht.2 hne
    have he : prepend b γ η =ᶠ[𝓝 t] γ := by
      filter_upwards [Iio_mem_nhds hlt] with s hs
      exact if_pos hs.le
    simp [F,coframeSpeed,he.deriv_eq,he.eq_of_nhds]
  have hright : ∀ᵐ t ∂(volume.restrict (Ioc b (b+c))),
      F t = ENNReal.ofReal (coframeSpeed d η (t-b)) := by
    filter_upwards [ae_restrict_mem (s:=Ioc b (b+c)) measurableSet_Ioc] with t ht
    have he : prepend b γ η =ᶠ[𝓝 t] (fun s => η (s-b)) := by
      filter_upwards [Ioi_mem_nhds ht.1] with s hs
      exact if_neg (not_le_of_gt hs)
    simp [F,coframeSpeed,he.deriv_eq,he.eq_of_nhds,deriv_comp_sub_const]
  change (∫⁻ t in Ioc (0:ℝ) (b+c), F t) = acLength d γ b+acLength d η c
  rw [←Ioc_union_Ioc_eq_Ioc hb (by linarith : b≤b+c),lintegral_union measurableSet_Ioc hdis,
    lintegral_congr_ae hleft,lintegral_congr_ae hright]
  exact congrArg (fun r => acLength d γ b+r)
    (translate_length (b:=b) (c:=c) (fun s => ENNReal.ofReal (coframeSpeed d η s)))

/-- Prepending a retained characteristic controls the buffer against every
absolutely continuous first exit, including infinite-length tails. -/
theorem source_buffer_after_directed {D : Set Plane} {d : Plane → ℝ} {z σ b M : ℝ}
    (hb : 0≤b) (hσ : |σ|=1) {y : ℝ → ℝ}
    (hy : DirectedSolution D d z σ 0 b y) (hLip : LipschitzPath (directedPoint z σ y) b)
    (hbuffer : HasACBuffer D d (directedPoint z σ y 0) M) :
    HasACBuffer D d (directedPoint z σ y b) (M-b) := by
  intro c η hη
  obtain ⟨hc,hη0,hηAC,hηD,hηExit⟩ := hη
  let γ := directedPoint z σ y
  have hjoin : γ b=η 0 := hη0.symm
  have hAC := prepend_ac hb hc (lipschitz_acPath hLip) hηAC hjoin
  have hstart : prepend b γ η 0=γ 0 := by simp [prepend,hb]
  have hD' : ∀ t ∈ Ico 0 (b+c), prepend b γ η t ∈ D := by
    intro t ht
    by_cases h : t≤b
    · simp only [prepend,if_pos h]
      exact (hy t ⟨ht.1,h⟩).1
    · have h' := le_of_not_ge h
      rw [prepend_eq_right hjoin h']
      exact hηD _ ⟨sub_nonneg.mpr h',by linarith [ht.2]⟩
  have hEnd : prepend b γ η (b+c)∉D := by
    rw [prepend_eq_right hjoin (by linarith : b≤b+c),add_sub_cancel_left]
    exact hηExit
  have hM := hbuffer (b+c) _ ⟨add_nonneg hb hc,hstart,hAC,hD',hEnd⟩
  have hγL : acLength d γ b=ENNReal.ofReal b :=
    directed_acLength hb hσ fun t ht =>
      (hy t (Ioo_subset_Icc_self ht)).2.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  rw [prepend_length hb hc,hγL] at hM
  rw [ENNReal.ofReal_sub _ hb]
  exact tsub_le_iff_right.mpr (by simpa [add_comm] using hM)

end PaperI.BoundedCharacteristic
