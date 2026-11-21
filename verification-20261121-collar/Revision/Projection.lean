import Revision.CapInterval

open Set Filter MeasureTheory
open scoped Topology
noncomputable section

namespace PaperI.CollarRevision

open BoundedCharacteristic ShortProjectionCaps ParabolicCollar CorridorBands

def horizontalForm (d : Plane → ℝ) (p : Plane) : Plane →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ - d p • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- First-order expansion for moving the initial point to a fixed nearby height. -/
private theorem initial_projection_deriv {Ω : Set Plane} {F : Plane → ℝ → ℝ} {d : Plane → ℝ}
    {p : Plane} (hp : p ∈ Ω) (hd : ContinuousAt d p) {K T : ℝ} (hK : 0 ≤ K) (hT : 0 < T)
    (hInit : ∀ q∈Ω, F q 0=q.1)
    (hTaylor : ∀ q∈Ω, ∀ t∈window T, |t|≤1 → |F q t-(q.1+d q*t)|≤K*|t|^2) :
    HasFDerivWithinAt (fun q : Plane => F q (p.2-q.2)) (horizontalForm d p) Ω p := by
  let t := fun q : Plane => p.2-q.2
  have ht : Tendsto t (𝓝[Ω] p) (𝓝 0) := by
    have h : Continuous (fun q : Plane => p.2-q.2) := continuous_const.sub continuous_snd
    simpa [t] using (h.continuousAt (x:=p)).tendsto.mono_left (nhdsWithin_le_nhds (s:=Ω))
  have hw : ∀ᶠ q in 𝓝[Ω] p, t q∈window T := ht.eventually (Icc_mem_nhds (by linarith) hT)
  have hsmall : ∀ᶠ q in 𝓝[Ω] p, |t q|≤1 := ht.abs.eventually_le_const (by norm_num)
  have hD : Tendsto (fun q => d q-d p) (𝓝[Ω] p) (𝓝 0) := by
    simpa using hd.continuousWithinAt.tendsto.sub (tendsto_const_nhds (x:=d p))
  rw [hasFDerivWithinAt_iff_tendsto]
  apply squeeze_zero' (Eventually.of_forall (fun q => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)))
      (g:=fun q => |d q-d p|+K*|t q|)
  · filter_upwards [self_mem_nhdsWithin,hw,hsmall] with q hq hqw hq1
    simp only [sub_self,hInit p hp,Real.norm_eq_abs]
    change ‖q-p‖⁻¹ * |F q (t q)-p.1-((q.1-p.1)-d p*(q.2-p.2))| ≤ _
    have hId : F q (t q)-p.1-((q.1-p.1)-d p*(q.2-p.2)) =
        (F q (t q)-(q.1+d q*t q))+(d q-d p)*t q := by dsimp [t]; ring
    have hStep : |t q| ≤ ‖q-p‖ := by
      dsimp only [t]
      rw [abs_sub_comm]
      exact (norm_snd_le (q-p))
    have hG : 0 ≤ |d q-d p|+K*|t q| := by positivity
    rw [hId]
    by_cases h : ‖q-p‖=0
    · simpa [h] using hG
    · apply (inv_mul_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))).mpr
      calc
        _ ≤ |F q (t q)-(q.1+d q*t q)|+|(d q-d p)*t q| := abs_add .. 
        _ ≤ K*|t q|^2+|d q-d p| *|t q| := by rw [abs_mul]; exact add_le_add_right (hTaylor q hq _ hqw hq1) _
        _ = (|d q-d p|+K*|t q|)*|t q| := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_left hStep hG).trans_eq (mul_comm ..)
  · simpa using hD.abs.add (ht.abs.const_mul K)

/-- The derivative is a positive multiple of the horizontal coframe for the actual ODE projection. -/
theorem projection_derivative {P m δ : ℝ} {C : ℕ} {D Ω : Set Plane} {d v : Plane → ℝ}
    {F : Plane → ℝ → ℝ} {z₀ : ℝ} (hP : 2≤P) (hm : 1≤m) (hδ : 0≤δ)
    (hD : IsOpen D) (hd : ∀ p∈D,ContDiffAt ℝ 1 d p) (hv : ∀ p∈D,DifferentiableAt ℝ v p)
    (hZ : ∀ p∈D,fderiv ℝ d p (d p,1)=v p)
    (hu : ∀ p∈D,|fderiv ℝ d p (1,0)|≤P^C*δ)
    (hZv : ∀ p∈D,|fderiv ℝ v p (d p,1)|≤P^C*δ) (hV : ∀ p∈D,|v p|≤P^C)
    (hs : (P^C*δ)*(2*m)≤Real.log 2)
    (hF : ∀ q∈Ω,F q 0=q.1 ∧ DirectedSolution D d q.2 1 (-(2*m)) (2*m) (F q))
    (hz : ∀ q∈Ω, |z₀-q.2|≤2*m) (p : Plane) (hp : p∈Ω) :
    ∃ J : ℝ, 1/2≤J ∧ J≤2 ∧
      HasFDerivWithinAt (fun q : Plane => F q (z₀-q.2)) (J • horizontalForm d p) Ω p := by
  let T := 2*m
  have hT : 0<T := by dsimp [T]; linarith
  have h0 : (0:ℝ)∈window T := ⟨by linarith,hT.le⟩
  have hIn (q : Plane) (hq : q∈Ω) : q∈D := by
    simpa [directedPoint,(hF q hq).1] using ((hF q hq).2 0 h0).1
  have h₀ : 0≤P^C*δ := mul_nonneg (pow_nonneg (by linarith) _) hδ
  let K := P^C*δ+P^C
  have hK : 0≤K := add_nonneg h₀ (pow_nonneg (by linarith) _)
  have hTaylor (q : Plane) (hq : q∈Ω) (t : ℝ) (ht : t∈window T) (ht₁ : |t|≤1) :
      |F q t-(q.1+d q*t)|≤K*|t|^2 := by
    have hh := (characteristic_taylor h₀ (fun u hu' => (hd u hu').differentiableAt (by simp))
      hv hZ hZv (hF q hq).2 t ht).2
    simp only [(hF q hq).1,point,add_zero,Prod.mk.eta] at hh
    have he : F q t-(q.1+d q*t)=(F q t-(q.1+d q*t+v q*t^2/2))+v q*t^2/2 := by ring
    rw [he]
    have hvq := hV q (hIn q hq)
    have hh₃ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht₁ (sq_nonneg |t|)) h₀
    have hq₂ := mul_le_mul_of_nonneg_right hvq (sq_nonneg t)
    calc
      _ ≤ _ := abs_add .. 
      _ ≤ P^C*δ*|t|^3+|v q| *t^2/2 := by
        rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg t),abs_of_pos (by norm_num : (0:ℝ)<2)]
        exact add_le_add_right hh _
      _ ≤ _ := by
        dsimp [K]
        have hCube : |t|^3 ≤ |t|^2 := by nlinarith only [mul_le_mul_of_nonneg_left ht₁ (sq_nonneg |t|)]
        have h₃ := mul_le_mul_of_nonneg_left hCube h₀
        rw [sq_abs] at h₃ ⊢
        nlinarith only [h₃,hq₂,mul_nonneg (abs_nonneg (v q)) (sq_nonneg t)]
  let x := fun q : Plane => F q (p.2-q.2)
  have hx := initial_projection_deriv hp (hd p (hIn p hp)).continuousAt hK hT (fun q hq => (hF q hq).1) hTaylor
  have hxp : x p=p.1 := by simp [x,(hF p hp).1]
  obtain ⟨k,hk⟩ := constant_frame_comparison
  obtain ⟨G,r,hr,hG,hNear,hDer⟩ := (bounded_time_characteristic_comparison hP hm hδ C D hD d hd
    (fun _ => True) (fun _ _ => trivial) (fun _ _ => 0) k (fun a _ b _ => hk hP a b)
    hs (fun u hu' => ⟨hu u hu',by rw [hZ u hu']; exact hV u hu'⟩)).1 p.2 (F p) (hF p hp).2
  have htime := abs_le.mp (hz p hp)
  obtain ⟨hDer',_,hJ₁,hJ₂,_⟩ := hDer _ htime
  rw [(hF p hp).1] at hDer'
  let J := Real.exp (∫ t in (0:ℝ)..(z₀-p.2), fderiv ℝ d (point (F p) p.2 t) (1,0))
  refine ⟨J,hJ₁,hJ₂,?_⟩
  have hxlim : Tendsto x (𝓝[Ω] p) (𝓝 p.1) := hxp ▸ hx.continuousWithinAt
  have hNearX : ∀ᶠ q in 𝓝[Ω] p, |x q-p.1|<r := hxlim.eventually (by
    simpa [Real.dist_eq] using Metric.ball_mem_nhds p.1 hr)
  have htlim : Tendsto (fun q : Plane => p.2-q.2) (𝓝[Ω] p) (𝓝 0) := by
    have h : Continuous (fun q : Plane => p.2-q.2) := continuous_const.sub continuous_snd
    simpa using (h.continuousAt (x:=p)).tendsto.mono_left (nhdsWithin_le_nhds (s:=Ω))
  have hWin := htlim.eventually (Icc_mem_nhds (show -T<0 by linarith) hT)
  have hEq : (fun q : Plane => F q (z₀-q.2)) =ᶠ[𝓝[Ω] p] (fun q => G (x q) (z₀-p.2)) := by
    filter_upwards [hNearX,hWin,self_mem_nhdsWithin] with q hqr hqw hq
    obtain ⟨hg₀,hg⟩ := hNear (x q) (by simpa [(hF p hp).1] using hqr)
    exact rebase_agrees hd (q:=p.2) (hF q hq).2 hg hqw (by simpa using h0)
      (abs_le.mp (hz q hq)) htime (by simpa [x] using hg₀.symm)
  have hAt : HasDerivAt (fun u => G u (z₀-p.2)) J (x p) := hxp.symm ▸ hDer'
  apply (hEq.hasFDerivWithinAt_iff_of_mem hp).mpr
  have hh := hAt.hasFDerivAt.comp_hasFDerivWithinAt p hx
  have heq : J • horizontalForm d p = (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) J).comp (horizontalForm d p) := by
    apply ContinuousLinearMap.ext
    intro u
    exact mul_comm J (horizontalForm d p u)
  rw [heq]
  exact hh

end PaperI.CollarRevision
