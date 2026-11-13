import PaperILean.BoundedCharacteristicVariational
import Mathlib.Analysis.ODE.Gronwall

open Set Filter Metric MeasureTheory
open scoped Topology NNReal

noncomputable section

namespace PaperI.BoundedCharacteristic

/-- Direction is +1 for forward time and -1 for reverse time. The equation is
taken on the closed parameter interval, including one-sided endpoints. -/
def directedPoint (z σ : ℝ) (y : ℝ → ℝ) (t : ℝ) : Plane := (y t,z+σ*t)

def DirectedSolution (D : Set Plane) (d : Plane → ℝ) (z σ a b : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ t ∈ Icc a b,
    directedPoint z σ y t ∈ D ∧
      HasDerivWithinAt y (σ*d (directedPoint z σ y t)) (Icc a b) t

/-- Finite Lipschitz regularity on a compact path interval. It suffices for
absolute continuity and includes the limiting endpoint of a first exit. -/
def LipschitzPath (γ : ℝ → Plane) (T : ℝ) : Prop :=
  ∃ K : ℝ≥0, LipschitzOnWith K γ (Icc 0 T)

def coframeSpeed (d : Plane → ℝ) (γ : ℝ → Plane) (t : ℝ) : ℝ :=
  |(deriv γ t).1-d (γ t)*(deriv γ t).2|+|(deriv γ t).2|

def coframeLength (d : Plane → ℝ) (γ : ℝ → Plane) (T : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..T, coframeSpeed d γ t

/-- First-exit paths used in the buffer argument. For the local comparison
proof only Lipschitz paths with integrable speed are needed; all such paths
are included in the original absolutely continuous first-exit condition. -/
def FirstExit (D : Set Plane) (d : Plane → ℝ) (p : Plane) (T : ℝ) (γ : ℝ → Plane) : Prop :=
  0 ≤ T ∧ γ 0 = p ∧ LipschitzPath γ T ∧
    IntervalIntegrable (coframeSpeed d γ) volume 0 T ∧
    (∀ t ∈ Ico 0 T, γ t ∈ D) ∧ γ T ∉ D

def HasBuffer (D : Set Plane) (d : Plane → ℝ) (p : Plane) (M : ℝ) : Prop :=
  ∀ T γ, FirstExit D d p T γ → M ≤ coframeLength d γ T

private theorem locallyLipschitz_field {D : Set Plane} {d : Plane → ℝ} {σ : ℝ}
    (hd : ∀ p ∈ D, ContDiffAt ℝ 1 d p) {p : Plane} (hp : p ∈ D) :
    ∃ K : ℝ≥0, ∃ r > 0, LipschitzOnWith K (fun p : Plane => σ*d p) (ball p r) := by
  have h := (contDiffAt_const.mul (hd p hp) : ContDiffAt ℝ 1 (fun p => σ*d p) p)
  obtain ⟨K,s,hs,hLip⟩ := (h.hasStrictFDerivAt (by norm_num)).exists_lipschitzOnWith
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hs
  exact ⟨K,r,hr,hLip.mono hrs⟩

private theorem local_directed_solution {D : Set Plane} (hD : IsOpen D) {d : Plane → ℝ}
    (hd : ∀ p ∈ D, ContDiffAt ℝ 1 d p) {z σ t₀ y₀ : ℝ}
    (h₀ : (y₀,z+σ*t₀) ∈ D) :
    ∃ y : ℝ → ℝ, y t₀ = y₀ ∧ ∃ ε > 0, ∀ t ∈ Ioo (t₀-ε) (t₀+ε),
      directedPoint z σ y t ∈ D ∧ HasDerivAt y (σ*d (directedPoint z σ y t)) t := by
  let v := fun t y => σ*d (y,z+σ*t)
  have hreg : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => v p.1 p.2) (t₀,y₀) := by
    have hmap : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (p.2,z+σ*p.1)) (t₀,y₀) := by fun_prop
    exact contDiffAt_const.mul ((hd _ h₀).comp (t₀,y₀) hmap)
  obtain ⟨y,hy0,ε,hε,hy⟩ := PaperI.exists_local_nonautonomous_solution v t₀ y₀ hreg
  have ht₀ : t₀ ∈ Ioo (t₀-ε) (t₀+ε) := ⟨by linarith,by linarith⟩
  have hpoint : ContinuousAt (directedPoint z σ y) t₀ :=
    (hy _ ht₀).continuousAt.prodMk (by fun_prop)
  have hpre : directedPoint z σ y ⁻¹' D ∈ 𝓝 t₀ :=
    hpoint (hD.mem_nhds (by simpa [directedPoint,hy0] using h₀))
  obtain ⟨δ,hδ,hδD⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨y,hy0,min ε δ,lt_min hε hδ,?_⟩
  intro t ht
  have htε : t ∈ Ioo (t₀-ε) (t₀+ε) := by
    constructor
    · linarith [ht.1,min_le_left ε δ]
    · linarith [ht.2,min_le_left ε δ]
  have htδ : t ∈ ball t₀ δ := by
    rw [mem_ball,Real.dist_eq,abs_lt]
    constructor
    · linarith [ht.1,min_le_right ε δ]
    · linarith [ht.2,min_le_right ε δ]
  exact ⟨hδD htδ,hy t htε⟩

/-- Equality of two actual branch solutions on their common initial interval.
At any common point both trajectories lie in one small Lipschitz box;
the forward and reversed Gronwall uniqueness results give openness of the
equality set relative to the interval, including its endpoints. -/
theorem directed_solution_unique {D : Set Plane} {d : Plane → ℝ}
    (hd : ∀ p ∈ D, ContDiffAt ℝ 1 d p) {z σ a b : ℝ} (hab : a ≤ b)
    {f g : ℝ → ℝ} (hf : DirectedSolution D d z σ a b f)
    (hg : DirectedSolution D d z σ a b g) (hfg : f a = g a) :
    EqOn f g (Icc a b) := by
  let I := Icc a b
  let U : Set I := {t | f t = g t}
  have hcf : ContinuousOn f I := fun t ht => (hf t ht).2.continuousWithinAt
  have hcg : ContinuousOn g I := fun t ht => (hg t ht).2.continuousWithinAt
  have hUf : IsClosed U :=
    isClosed_eq (continuousOn_iff_continuous_restrict.mp hcf)
      (continuousOn_iff_continuous_restrict.mp hcg)
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have ht' : f t = g t := ht
    let p := directedPoint z σ f t
    obtain ⟨K,r,hr,hLip⟩ := locallyLipschitz_field (d:=d) (σ:=σ) hd (hf t t.2).1
    have hpf : ContinuousOn (directedPoint z σ f) I := hcf.prodMk (by fun_prop)
    have hpg : ContinuousOn (directedPoint z σ g) I := hcg.prodMk (by fun_prop)
    have hpgEq : directedPoint z σ g t = p := by simp [directedPoint,p,ht']
    have hpreF : directedPoint z σ f ⁻¹' ball p r ∈ 𝓝[I] (t:ℝ) :=
      (hpf t t.2).preimage_mem_nhdsWithin (Metric.ball_mem_nhds _ hr)
    have hpreG : directedPoint z σ g ⁻¹' ball p r ∈ 𝓝[I] (t:ℝ) := by
      apply (hpg t t.2).preimage_mem_nhdsWithin
      rw [hpgEq]
      exact Metric.ball_mem_nhds _ hr
    have hboth : ∀ᶠ s in 𝓝 (t:ℝ), s ∈ I →
        directedPoint z σ f s ∈ ball p r ∧ directedPoint z σ g s ∈ ball p r :=
      eventually_nhdsWithin_iff.mp (show ∀ᶠ s in 𝓝[I] (t:ℝ),
        directedPoint z σ f s ∈ ball p r ∧ directedPoint z σ g s ∈ ball p r from
        Filter.inter_mem hpreF hpreG)
    obtain ⟨ε,hε,hεp⟩ := Metric.eventually_nhds_iff.mp hboth
    apply (mem_nhds_subtype I t U).mpr
    refine ⟨ball (t:ℝ) ε,Metric.ball_mem_nhds _ hε,?_⟩
    intro s hs
    have hclose : |(s:ℝ)-(t:ℝ)| < ε := by
      simpa [Metric.mem_ball,Real.dist_eq] using hs
    have him := fun q hq hqI => hεp
      (show dist q (t:ℝ) < ε by simpa only [Real.dist_eq] using hq) hqI
    let v := fun q x => σ*d (x,z+σ*q)
    let B := fun q => {x | (x,z+σ*q) ∈ ball p r}
    have hvlip : ∀ q, LipschitzOnWith K (v q) (B q) := by
      intro q
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx x' hx'
      have h := hLip.dist_le_mul _ hx _ hx'
      change dist (v q x) (v q x') ≤ ↑K*dist x x'
      change dist (v q x) (v q x') ≤ ↑K*dist (x,z+σ*q) (x',z+σ*q) at h
      simpa [Prod.dist_eq,max_eq_left (dist_nonneg (x:=x) (y:=x'))] using h
    show f s = g s
    by_cases hts : (t:ℝ) ≤ s
    · have hsub : Icc (t:ℝ) (s:ℝ) ⊆ I := Icc_subset_Icc t.2.1 s.2.2
      have hmem : ∀ q ∈ Icc (t:ℝ) (s:ℝ), f q ∈ B q ∧ g q ∈ B q := by
        intro q hq
        apply him q _ (hsub hq)
        rw [abs_of_nonneg (sub_nonneg.mpr hq.1)]
        have hcs := (abs_lt.mp hclose).2
        linarith [hq.2]
      apply ODE_solution_unique_of_mem_Icc_right (v:=v) (s:=B)
        (fun q _ => hvlip q) (hcf.mono hsub) _ _ (hcg.mono hsub) _ _ ht'
        (right_mem_Icc.mpr hts)
      · intro q hq
        exact ((hf q (hsub (Ico_subset_Icc_self hq))).2.mono hsub).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem hq)
      · intro q hq
        exact (hmem q (Ico_subset_Icc_self hq)).1
      · intro q hq
        exact ((hg q (hsub (Ico_subset_Icc_self hq))).2.mono hsub).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem hq)
      · intro q hq
        exact (hmem q (Ico_subset_Icc_self hq)).2
    · have hst := le_of_not_ge hts
      have hsub : Icc (s:ℝ) (t:ℝ) ⊆ I := Icc_subset_Icc s.2.1 t.2.2
      have hmem : ∀ q ∈ Icc (s:ℝ) (t:ℝ), f q ∈ B q ∧ g q ∈ B q := by
        intro q hq
        apply him q _ (hsub hq)
        rw [abs_of_nonpos (sub_nonpos.mpr hq.2)]
        have hcs := (abs_lt.mp hclose).1
        linarith [hq.1]
      apply ODE_solution_unique_of_mem_Icc_left (v:=v) (s:=B)
        (fun q _ => hvlip q) (hcf.mono hsub) _ _ (hcg.mono hsub) _ _ ht'
        (left_mem_Icc.mpr hst)
      · intro q hq
        exact ((hf q (hsub (Ioc_subset_Icc_self hq))).2.mono hsub).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem hq)
      · intro q hq
        exact (hmem q (Ioc_subset_Icc_self hq)).1
      · intro q hq
        exact ((hg q (hsub (Ioc_subset_Icc_self hq))).2.mono hsub).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem hq)
      · intro q hq
        exact (hmem q (Ioc_subset_Icc_self hq)).2
  letI : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hUn : U.Nonempty := ⟨⟨a,left_mem_Icc.mpr hab⟩,hfg⟩
  have hU : U = univ := IsClopen.eq_univ ⟨hUf,hUo⟩ hUn
  intro t ht
  exact (show (⟨t,ht⟩:I) ∈ U by rw [hU]; trivial)

private theorem local_directed_solution_pos {D : Set Plane} (hD : IsOpen D) {d : Plane → ℝ}
    (hd : ∀ p ∈ D, ContDiffAt ℝ 1 d p) {z σ t₀ y₀ : ℝ}
    (h₀ : (y₀,z+σ*t₀) ∈ D) :
    ∃ y : ℝ → ℝ, y t₀ = y₀ ∧ ∃ ε > 0, DirectedSolution D d z σ t₀ (t₀+ε) y := by
  obtain ⟨y,hy,ε,hε,h⟩ := local_directed_solution hD hd h₀
  refine ⟨y,hy,ε/2,by positivity,fun t ht => ?_⟩
  have hmem : t ∈ Ioo (t₀-ε) (t₀+ε) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  exact ⟨(h t hmem).1,(h t hmem).2.hasDerivWithinAt⟩

private theorem restrict_solution {D : Set Plane} {d : Plane → ℝ} {z σ a b a' b' : ℝ}
    {y : ℝ → ℝ} (hy : DirectedSolution D d z σ a b y) (ha : a≤a') (hb : b'≤b) :
    DirectedSolution D d z σ a' b' y := fun t ht =>
  ⟨(hy t (Icc_subset_Icc ha hb ht)).1,(hy t (Icc_subset_Icc ha hb ht)).2.mono (Icc_subset_Icc ha hb)⟩

theorem join_directed_solution {D : Set Plane} {d : Plane → ℝ} {z σ a b c : ℝ}
    (hab : a≤b) (hbc : b≤c) {f g : ℝ → ℝ}
    (hf : DirectedSolution D d z σ a b f) (hg : DirectedSolution D d z σ b c g)
    (he : f b = g b) :
    DirectedSolution D d z σ a c (fun t => if t≤b then f t else g t) := by
  let y := fun t => if t≤b then f t else g t
  have hyl : EqOn y f (Icc a b) := fun t ht => by simp [y,ht.2]
  have hyr : EqOn y g (Icc b c) := by
    intro t ht
    by_cases h : t≤b
    · have ht' : t=b := le_antisymm h ht.1
      subst t
      simpa [y] using he
    · simp [y,h]
  have hset : Icc a b ∪ Icc b c = Icc a c := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact ⟨ht.1,ht.2.trans hbc⟩
      · exact ⟨hab.trans ht.1,ht.2⟩
    · intro ht
      by_cases h : t≤b
      · exact Or.inl ⟨ht.1,h⟩
      · exact Or.inr ⟨le_of_not_ge h,ht.2⟩
  intro t ht
  change directedPoint z σ y t ∈ D ∧ _
  rcases lt_trichotomy t b with ht' | rfl | ht'
  · have hl : t ∈ Icc a b := ⟨ht.1,ht'.le⟩
    have hye : directedPoint z σ y t = directedPoint z σ f t := by simp [directedPoint,hyl hl]
    rw [hye]
    refine ⟨(hf t hl).1,?_⟩
    have hd := (hf t hl).2.congr hyl (hyl hl)
    apply hd.mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht')] with s hs hsb
    exact ⟨hs.1,hsb.le⟩
  · have hl : t ∈ Icc a t := right_mem_Icc.mpr hab
    have hr : t ∈ Icc t c := left_mem_Icc.mpr hbc
    have hye : directedPoint z σ y t = directedPoint z σ f t := by simp [directedPoint,hyl hl]
    have hfg : directedPoint z σ g t = directedPoint z σ f t := by simp [directedPoint,he]
    rw [hye]
    refine ⟨(hf t hl).1,?_⟩
    rw [← hset]
    have hdl := (hf t hl).2.congr hyl (hyl hl)
    have hdr := (hg t hr).2.congr hyr (hyr hr)
    rw [hfg] at hdr
    exact hdl.union hdr
  · have hr : t ∈ Icc b c := ⟨ht'.le,ht.2⟩
    have hye : directedPoint z σ y t = directedPoint z σ g t := by simp [directedPoint,hyr hr]
    rw [hye]
    refine ⟨(hg t hr).1,?_⟩
    have hd := (hg t hr).2.congr hyr (hyr hr)
    apply hd.mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht')] with s hs hbs
    exact ⟨hbs.le,hs.2⟩

private theorem along_solution_field_derivative {D : Set Plane} {d v : Plane → ℝ}
    (hd : ∀ p ∈ D, ContDiffAt ℝ 1 d p)
    (hv : ∀ p ∈ D, fderiv ℝ d p (d p,1)=v p)
    {z σ a b : ℝ} {y : ℝ → ℝ}
    (hy : DirectedSolution D d z σ a b y) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun t => d (directedPoint z σ y t))
      (σ*v (directedPoint z σ y t)) (Icc a b) t := by
  let p := directedPoint z σ y t
  have hp : p ∈ D := (hy t ht).1
  have hz : HasDerivWithinAt (fun t => z+σ*t) σ (Icc a b) t :=
    by simpa only [id_eq,mul_one] using
      (((hasDerivAt_id t).const_mul σ).const_add z).hasDerivWithinAt (s:=Icc a b)
  have hpath : HasDerivWithinAt (directedPoint z σ y) (σ*d p,σ) (Icc a b) t :=
    (hy t ht).2.prodMk hz
  have he : (σ*d p,σ) = σ • (d p,1) := by simp
  have hdd := ((hd p hp).differentiableAt (by norm_num)).hasFDerivAt
  have h := hdd.hasFDerivWithinAt.comp_hasDerivWithinAt t hpath
    (mapsTo_univ _ _)
  rw [he,map_smul,hv p hp] at h
  exact h

theorem solution_value_lipschitz {D : Set Plane} {d v : Plane → ℝ}
    (hd : ∀ p ∈ D, ContDiffAt ℝ 1 d p)
    (hv : ∀ p ∈ D, fderiv ℝ d p (d p,1)=v p)
    {V z σ b H y₀ : ℝ} (hV : ∀ p ∈ D, |v p|≤V) (hσ : |σ|=1)
    (hb : 0<b) (hbH : b≤H) {y : ℝ → ℝ}
    (hy0 : y 0=y₀) (hy : DirectedSolution D d z σ 0 b y) :
    ∀ t₁ ∈ Icc 0 b, ∀ t₂ ∈ Icc 0 b,
      |y t₁-y t₂| ≤ (|d (y₀,z)|+V*H)*|t₁-t₂| := by
  have hV0 : 0≤V := (abs_nonneg _).trans (hV _ (hy 0 ⟨le_rfl,hb.le⟩).1)
  let f := fun t => d (directedPoint z σ y t)
  have hfd : ∀ t ∈ Icc (0:ℝ) b,
      HasDerivWithinAt f (σ*v (directedPoint z σ y t)) (Icc 0 b) t :=
    fun t ht => along_solution_field_derivative hd hv hy ht
  have hfb : ∀ t ∈ Icc (0:ℝ) b, ‖derivWithin f (Icc 0 b) t‖≤V := by
    intro t ht
    rw [(hfd t ht).derivWithin (uniqueDiffOn_Icc hb t ht), Real.norm_eq_abs, abs_mul,hσ,one_mul]
    exact hV _ (hy t ht).1
  have hfb' : ∀ t ∈ Icc (0:ℝ) b, |f t|≤|d (y₀,z)|+V*H := by
    intro t ht
    have hm := Convex.norm_image_sub_le_of_norm_derivWithin_le
      (fun s hs => (hfd s hs).differentiableWithinAt) hfb (convex_Icc 0 b)
      (left_mem_Icc.mpr hb.le) ht
    rw [sub_zero,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ht.1] at hm
    have hf0 : f 0=d (y₀,z) := by simp [f,directedPoint,hy0]
    calc |f t|=|f t-f 0+f 0| := by ring_nf
         _ ≤ |f t-f 0|+|f 0| := abs_add _ _
         _ ≤ V*t+|d (y₀,z)| := by rw [hf0] at hm ⊢; linarith
         _ ≤ |d (y₀,z)|+V*H := by linarith [mul_le_mul_of_nonneg_left (ht.2.trans hbH) hV0]
  have hyb : ∀ t ∈ Icc (0:ℝ) b, ‖derivWithin y (Icc 0 b) t‖≤|d (y₀,z)|+V*H := by
    intro t ht
    rw [(hy t ht).2.derivWithin (uniqueDiffOn_Icc hb t ht),Real.norm_eq_abs,abs_mul,hσ,one_mul]
    exact hfb' t ht
  intro t₁ h₁ t₂ h₂
  have hm := Convex.norm_image_sub_le_of_norm_derivWithin_le
    (fun s hs => (hy s hs).2.differentiableWithinAt) hyb (convex_Icc 0 b) h₂ h₁
  simpa [Real.norm_eq_abs] using hm

private theorem interval_integrable_extend_endpoint {f : ℝ → ℝ} {b c : ℝ}
    (hc : ContinuousOn f (Icc b c)) (hbc : b≤c) :
    IntervalIntegrable f volume b c :=
  (by simpa only [uIcc_of_le hbc] using hc : ContinuousOn f (uIcc b c)).intervalIntegrable

private theorem ae_ne_point (b : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
  rw [ae_iff]
  simp

theorem directed_interior_speed {d : Plane → ℝ} {z σ b : ℝ} {y : ℝ → ℝ}
    (hσ : |σ|=1)
    (hy : ∀ t ∈ Ioo (0:ℝ) b,
      HasDerivAt y (σ*d (directedPoint z σ y t)) t) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) b) :
    coframeSpeed d (directedPoint z σ y) t = 1 := by
  have hz : HasDerivAt (fun t => z+σ*t) σ t := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul σ).const_add z
  have hpath : HasDerivAt (directedPoint z σ y) (σ*d (directedPoint z σ y t),σ) t :=
    (hy t ht).prodMk hz
  rw [coframeSpeed,hpath.deriv]
  change |σ*d (directedPoint z σ y t)-d (directedPoint z σ y t)*σ|+|σ|=1
  rw [mul_comm σ,sub_self,abs_zero,zero_add,hσ]

theorem directed_length_of_interior {d : Plane → ℝ} {z σ b : ℝ} {y : ℝ → ℝ}
    (hb : 0≤b) (hσ : |σ|=1)
    (hy : ∀ t ∈ Ioo (0:ℝ) b, HasDerivAt y (σ*d (directedPoint z σ y t)) t) :
    IntervalIntegrable (coframeSpeed d (directedPoint z σ y)) volume 0 b ∧
      coframeLength d (directedPoint z σ y) b=b := by
  have he : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc (0:ℝ) b →
      coframeSpeed d (directedPoint z σ y) t=1 := by
    filter_upwards [ae_ne_point b] with t ht hmem
    rw [uIoc_of_le hb] at hmem
    exact directed_interior_speed hσ hy ⟨hmem.1,lt_of_le_of_ne hmem.2 ht⟩
  have hcongr : (fun _ : ℝ => (1:ℝ)) =ᵐ[volume.restrict (uIoc (0:ℝ) b)]
      coframeSpeed d (directedPoint z σ y) :=
    ((ae_restrict_iff' measurableSet_uIoc).mpr he).mono (fun _ h => h.symm)
  constructor
  · exact (continuous_const.intervalIntegrable 0 b).congr hcongr
  · rw [coframeLength,intervalIntegral.integral_congr_ae he,intervalIntegral.integral_const]
    simp

theorem directedPoint_lipschitz {z σ b : ℝ} {y : ℝ → ℝ} {K : ℝ≥0}
    (hσ : |σ|=1) (hy : LipschitzOnWith K y (Icc (0:ℝ) b)) :
    LipschitzPath (directedPoint z σ y) b := by
  refine ⟨max K 1,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx t ht
  rw [Prod.dist_eq]
  change max (dist (y x) (y t)) (dist (z+σ*x) (z+σ*t)) ≤ ↑(max K 1)*dist x t
  have h₁ := (hy.dist_le_mul x hx t ht).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K (1:ℝ≥0)) dist_nonneg)
  have hz : dist (z+σ*x) (z+σ*t)=dist x t := by
    simp only [Real.dist_eq]
    rw [show z+σ*x-(z+σ*t)=σ*(x-t) by ring,abs_mul,hσ,one_mul]
  rw [hz]
  exact max_le h₁ (by
    have h₂ : (1:ℝ)≤↑(max K 1) := by exact_mod_cast le_max_right K (1:ℝ≥0)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h₂ (dist_nonneg (x:=x) (y:=t)))

private theorem close_endpoint_derivative {b : ℝ} (hb : 0<b) {y f : ℝ → ℝ}
    (hy : ContinuousOn y (Icc 0 b)) (hf : ContinuousOn f (Icc 0 b))
    (hd : ∀ t ∈ Ioo (0:ℝ) b, HasDerivAt y (f t) t) :
    HasDerivWithinAt y (f b) (Icc 0 b) b := by
  let f' := fun t => f (projIcc 0 b hb.le t)
  have hfc : Continuous f' :=
    (continuousOn_iff_continuous_restrict.mp hf).comp continuous_projIcc
  have hfe : EqOn f' f (Icc 0 b) := by
    intro t ht
    exact congrArg f (congrArg Subtype.val (projIcc_of_mem hb.le ht))
  have he : EqOn y (fun t => y 0 + ∫ s in (0:ℝ)..t, f' s) (Icc 0 b) := by
    intro t ht
    have hsub : Icc (0:ℝ) t ⊆ Icc 0 b := Icc_subset_Icc le_rfl ht.2
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hy.mono hsub)
      (f' := f') (fun s hs => by
        rw [hfe (hsub (Ioo_subset_Icc_self hs))]
        exact hd s ⟨hs.1,hs.2.trans_le ht.2⟩)
      (hfc.intervalIntegrable 0 t)
    simp only
    rw [hFTC]
    ring
  have hh := intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable 0 b)
    hfc.stronglyMeasurable.stronglyMeasurableAtFilter hfc.continuousAt
  have hbe : b ∈ Icc (0:ℝ) b := right_mem_Icc.mpr hb.le
  rw [hfe hbe] at hh
  exact (hh.const_add (y 0)).hasDerivWithinAt.congr he (he hbe)

/-- A genuine finite-time continuation argument for the original scalar
characteristic equation. The buffer rules out actual first exit, not just
a shorter open parameter interval. -/
theorem directed_continuation_with_exit_control {D : Set Plane} (hD : IsOpen D) {d v : Plane → ℝ}
    (hd : ∀ p ∈ D, ContDiffAt ℝ 1 d p)
    (hv : ∀ p ∈ D, fderiv ℝ d p (d p,1)=v p)
    {V z σ H y₀ M : ℝ} (hV : ∀ p ∈ D, |v p|≤V) (hσ : |σ|=1)
    (hH : 0<H) (hMH : H<M) (hp : (y₀,z) ∈ D)
    (hbuffer : ∀ b y, FirstExit D d (y₀,z) b (directedPoint z σ y) →
      (∀ t ∈ Ioo 0 b, HasDerivAt y (σ*d (directedPoint z σ y t)) t) →
      M ≤ coframeLength d (directedPoint z σ y) b) :
    ∃ y : ℝ → ℝ, y 0=y₀ ∧ DirectedSolution D d z σ 0 H y := by
  let S := {b : ℝ | 0<b ∧ b≤H ∧ ∃ f : ℝ → ℝ,
      f 0=y₀ ∧ DirectedSolution D d z σ 0 b f}
  obtain ⟨f,hf0,ε,hε,hf⟩ := local_directed_solution_pos (z:=z) (σ:=σ) (t₀:=0) hD hd (by simpa using hp)
  have hf' : DirectedSolution D d z σ 0 (min ε H) f :=
    restrict_solution hf le_rfl (by simp [min_le_left])
  have hSmin : min ε H ∈ S := ⟨lt_min hε hH,min_le_right _ _,f,hf0,hf'⟩
  have hSn : S.Nonempty := ⟨_,hSmin⟩
  have hSb : BddAbove S := ⟨H,fun _ hb => hb.2.1⟩
  let B := sSup S
  have hB : 0<B := (lt_min hε hH).trans_le (le_csSup hSb hSmin)
  have hBH : B≤H := csSup_le hSn fun b hb => hb.2.1
  have hlocal : ∀ t ∈ Ico (0:ℝ) B, ∃ b ∈ S, t<b := fun _ ht => exists_lt_of_lt_csSup hSn ht.2
  let chooseEnd := fun (t : Ico (0:ℝ) B) => Classical.choose (hlocal t t.2)
  have hEnd : ∀ t : Ico (0:ℝ) B, chooseEnd t ∈ S ∧ (t:ℝ)<chooseEnd t :=
    fun t => Classical.choose_spec (hlocal t t.2)
  let chooseSol := fun (b : S) => Classical.choose b.2.2.2
  have hSol : ∀ b : S, chooseSol b 0=y₀ ∧ DirectedSolution D d z σ 0 b (chooseSol b) :=
    fun b => Classical.choose_spec b.2.2.2
  let y := fun t : ℝ => if ht : t ∈ Ico 0 B then chooseSol ⟨chooseEnd ⟨t,ht⟩,(hEnd ⟨t,ht⟩).1⟩ t else 0
  have hpatch : ∀ b : S, ∀ t ∈ Ico (0:ℝ) B, t≤(b:ℝ) → y t=chooseSol b t := by
    intro b t ht htb
    let a : S := ⟨chooseEnd ⟨t,ht⟩,(hEnd ⟨t,ht⟩).1⟩
    have hta : t<(a:ℝ) := (hEnd ⟨t,ht⟩).2
    have hyt : y t=chooseSol a t := dif_pos ht
    rw [hyt]
    exact directed_solution_unique hd (le_min a.2.1.le b.2.1.le)
      (restrict_solution (hSol a).2 le_rfl (min_le_left _ _))
      (restrict_solution (hSol b).2 le_rfl (min_le_right _ _))
      ((hSol a).1.trans (hSol b).1.symm) ⟨ht.1,le_min hta.le htb⟩
  have hy0 : y 0=y₀ := by
    let b : S := ⟨hSn.some,hSn.some_mem⟩
    exact (hpatch b 0 ⟨le_rfl,hB⟩ b.2.1.le).trans (hSol b).1
  have hyMem : ∀ t ∈ Ico (0:ℝ) B, directedPoint z σ y t ∈ D := by
    intro t ht
    let b : S := ⟨chooseEnd ⟨t,ht⟩,(hEnd ⟨t,ht⟩).1⟩
    have htb : t<(b:ℝ) := (hEnd ⟨t,ht⟩).2
    have he : directedPoint z σ y t=directedPoint z σ (chooseSol b) t := by
      simp only [directedPoint,hpatch b t ht htb.le]
    rw [he]
    exact ((hSol b).2 t ⟨ht.1,htb.le⟩).1
  have hV0 : 0≤V := (abs_nonneg _).trans (hV _ hp)
  let K : ℝ≥0 := ⟨|d (y₀,z)|+V*H,by positivity⟩
  have hLip : LipschitzOnWith K y (Ico (0:ℝ) B) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht t' ht'
    have hm : max t t' ∈ Ico (0:ℝ) B := ⟨ht.1.trans (le_max_left _ _),max_lt ht.2 ht'.2⟩
    obtain ⟨b,hb,hbt⟩ := hlocal (max t t') hm
    let c : S := ⟨b,hb⟩
    have htc : t ≤ (c:ℝ) := (le_max_left _ _).trans hbt.le
    have htc' : t' ≤ (c:ℝ) := (le_max_right _ _).trans hbt.le
    rw [hpatch c t ht htc,hpatch c t' ht' htc',Real.dist_eq,Real.dist_eq]
    exact solution_value_lipschitz hd hv hV hσ c.2.1 c.2.2.1 (hSol c).1 (hSol c).2
      t ⟨ht.1,htc⟩ t' ⟨ht'.1,htc'⟩
  obtain ⟨Y,hYL,hYe⟩ := hLip.extend_real
  have hY0 : Y 0=y₀ := (hYe ⟨le_rfl,hB⟩).symm.trans hy0
  have hYMem : ∀ t ∈ Ico (0:ℝ) B, directedPoint z σ Y t ∈ D := by
    intro t ht
    simpa only [directedPoint,← hYe ht] using hyMem t ht
  have hYDeriv : ∀ t ∈ Ioo (0:ℝ) B,
      HasDerivAt Y (σ*d (directedPoint z σ Y t)) t := by
    intro t ht
    obtain ⟨b,hb,hbt⟩ := hlocal t ⟨ht.1.le,ht.2⟩
    let c : S := ⟨b,hb⟩
    have he : Y =ᶠ[𝓝 t] chooseSol c := by
      filter_upwards [Ico_mem_nhds ht.1 ht.2,Icc_mem_nhds ht.1 hbt] with s hs hs'
      exact (hYe hs).symm.trans (hpatch c s hs hs'.2)
    have hder := ((hSol c).2 t ⟨ht.1.le,hbt.le⟩).2.hasDerivAt (Icc_mem_nhds ht.1 hbt)
    rw [show directedPoint z σ (chooseSol c) t=directedPoint z σ Y t by
      simp only [directedPoint,he.eq_of_nhds]] at hder
    exact he.symm.hasDerivAt_iff.mp hder
  have hYB : directedPoint z σ Y B ∈ D := by
    apply Classical.byContradiction
    intro hbad
    obtain ⟨hi,hlen⟩ := directed_length_of_interior hB.le hσ hYDeriv
    have hexit : FirstExit D d (y₀,z) B (directedPoint z σ Y) :=
      ⟨hB.le,by simp [directedPoint,hY0],directedPoint_lipschitz hσ hYL.lipschitzOnWith,
        hi,hYMem,hbad⟩
    have hM := hbuffer B Y hexit hYDeriv
    rw [hlen] at hM
    exact (not_le_of_gt (hBH.trans_lt hMH)) hM
  have hYMem' : ∀ t ∈ Icc (0:ℝ) B, directedPoint z σ Y t ∈ D := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with h | rfl
    · exact hYMem t ⟨ht.1,h⟩
    · exact hYB
  have hYDeriv0 : HasDerivWithinAt Y (σ*d (directedPoint z σ Y 0)) (Icc (0:ℝ) B) 0 := by
    let c : S := ⟨hSn.some,hSn.some_mem⟩
    have he : Y =ᶠ[𝓝[Icc (0:ℝ) B] 0] chooseSol c := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min hB c.2.1))] with t ht ht'
      exact (hYe ⟨ht.1,ht'.trans_le (min_le_left _ _)⟩).symm.trans
        (hpatch c t ⟨ht.1,ht'.trans_le (min_le_left _ _)⟩ (ht'.le.trans (min_le_right _ _)))
    have h0 : (0:ℝ) ∈ Icc 0 B := left_mem_Icc.mpr hB.le
    have hder := ((hSol c).2 0 ⟨le_rfl,c.2.1.le⟩).2
    have hh : Icc (0:ℝ) (c:ℝ) ∈ 𝓝[Icc (0:ℝ) B] 0 := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds c.2.1)] with t ht ht'
      exact ⟨ht.1,ht'.le⟩
    have hder' := hder.mono_of_mem_nhdsWithin hh
    rw [show directedPoint z σ (chooseSol c) 0=directedPoint z σ Y 0 by
      simp only [directedPoint,he.eq_of_nhdsWithin h0]] at hder'
    exact hder'.congr_of_eventuallyEq he (he.eq_of_nhdsWithin h0)
  have hYDerivB : HasDerivWithinAt Y (σ*d (directedPoint z σ Y B)) (Icc (0:ℝ) B) B := by
    have hcont : ContinuousOn (fun t => σ*d (directedPoint z σ Y t)) (Icc 0 B) := by
      have hc : ContinuousOn d D := fun p hp => (hd p hp).continuousAt.continuousWithinAt
      exact continuousOn_const.mul
        (hc.comp (hYL.continuous.continuousOn.prodMk (by fun_prop)) hYMem')
    exact close_endpoint_derivative hB hYL.continuous.continuousOn hcont hYDeriv
  have hYS : DirectedSolution D d z σ 0 B Y := by
    intro t ht
    refine ⟨hYMem' t ht,?_⟩
    rcases eq_or_lt_of_le ht.1 with rfl | hpos
    · exact hYDeriv0
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact (hYDeriv t ⟨hpos,hlt⟩).hasDerivWithinAt
    · exact hYDerivB
  have hBH' : B=H := by
    apply Classical.byContradiction
    intro hne
    have hlt : B<H := lt_of_le_of_ne hBH hne
    obtain ⟨g,hg,δ,hδ,hg'⟩ := local_directed_solution_pos hD hd hYB
    have hbd : B<min (B+δ) H := lt_min (by linarith) hlt
    have hjoined := join_directed_solution hB.le hbd.le hYS
      (restrict_solution hg' le_rfl (min_le_left _ _)) hg.symm
    have hS' : min (B+δ) H ∈ S :=
      ⟨hB.trans hbd,min_le_right _ _,_,by simp [hB.le,hY0],hjoined⟩
    exact (not_le_of_gt hbd) (le_csSup hSb hS')
  exact ⟨Y,hY0,hBH' ▸ hYS⟩

end PaperI.BoundedCharacteristic
