import PaperILean.BoundedCharacteristicComparison

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace PaperI.ParabolicCollar
open BoundedCharacteristic

private theorem local_window_bound {T K : ℝ} {f g : ℝ → ℝ}
    (h : ∀ x ∈ window T, HasDerivWithinAt f (g x) (window T) x)
    {t : ℝ} (ht : t ∈ window T)
    (hg : ∀ x ∈ window |t|, |g x| ≤ K) : |f t-f 0| ≤ K*|t| := by
  by_cases he : t=0
  · simp [he]
  have hr : 0 < |t| := abs_pos.mpr he
  have hsub : window |t| ⊆ window T := by
    intro x hx
    exact abs_le.mp ((abs_le.mpr hx).trans (abs_le.mpr ht))
  have hh := fun x hx => (h x (hsub hx)).mono hsub
  have hbound : ∀ x ∈ window |t|, ‖derivWithin f (window |t|) x‖ ≤ K := by
    intro x hx
    rw [(hh x hx).derivWithin (uniqueDiffOn_Icc (by linarith) x hx),Real.norm_eq_abs]
    exact hg x hx
  have h0 : (0:ℝ)∈window |t| := abs_le.mp (by simpa only [abs_zero] using hr.le)
  have ht' : t∈window |t| := abs_le.mp le_rfl
  simpa only [Real.norm_eq_abs,sub_zero] using
    Convex.norm_image_sub_le_of_norm_derivWithin_le (fun x hx => (hh x hx).differentiableWithinAt)
      hbound (convex_Icc _ _) h0 ht'

theorem characteristic_taylor {T h z : ℝ} {E : Set Plane} {d v : Plane → ℝ}
    (hh : 0≤h) (hd : ∀ p∈E, DifferentiableAt ℝ d p)
    (hv : ∀ p∈E, DifferentiableAt ℝ v p)
    (hZ : ∀ p∈E, fderiv ℝ d p (d p,1)=v p)
    (hrate : ∀ p∈E, |fderiv ℝ v p (d p,1)| ≤ h)
    {y : ℝ → ℝ} (hy : DirectedSolution E d z 1 (-T) T y) :
    ∀ t∈window T,
      |d (point y z t) - (d (point y z 0)+v (point y z 0)*t)| ≤ h*|t|^2 ∧
      |y t-(y 0+d (point y z 0)*t+v (point y z 0)*t^2/2)| ≤ h*|t|^3 := by
  let p := point y z
  let d₀ := d (p 0)
  let v₀ := v (p 0)
  have hp (s : ℝ) (hs : s∈window T) : p s∈E := by
    simpa [p,point,directedPoint] using (hy s hs).1
  have hyd (s : ℝ) (hs : s∈window T) : HasDerivWithinAt y (d (p s)) (window T) s := by
    simpa [p,point,directedPoint] using (hy s hs).2
  have hpd (s : ℝ) (hs : s∈window T) :
      HasDerivWithinAt p (d (p s),1) (window T) s := by
    exact (hyd s hs).prodMk (((hasDerivAt_id s).const_add z).hasDerivWithinAt)
  have hd' (s : ℝ) (hs : s∈window T) :
      HasDerivWithinAt (fun t => d (p t)) (v (p s)) (window T) s := by
    have hc := (hd _ (hp s hs)).hasFDerivAt.comp_hasDerivWithinAt s (hpd s hs)
    rw [hZ _ (hp s hs)] at hc
    exact hc
  have hv' (s : ℝ) (hs : s∈window T) :
      HasDerivWithinAt (fun t => v (p t)) (fderiv ℝ v (p s) (d (p s),1)) (window T) s :=
    (hv _ (hp s hs)).hasFDerivAt.comp_hasDerivWithinAt s (hpd s hs)
  have hvr (t : ℝ) (ht : t∈window T) : |v (p t)-v₀|≤h*|t| :=
    local_window_bound hv' ht (fun s hs => hrate _ (hp s (abs_le.mp ((abs_le.mpr hs).trans (abs_le.mpr ht)))))
  have hdr (t : ℝ) (ht : t∈window T) : |d (p t)-(d₀+v₀*t)|≤h*|t|^2 := by
    have hder : ∀ s∈window T, HasDerivWithinAt (fun t => d (p t)-(d₀+v₀*t))
        (v (p s)-v₀) (window T) s := by
      intro s hs
      simpa only [id_eq,mul_one] using (hd' s hs).sub
        (((hasDerivAt_id s).const_mul v₀).const_add d₀).hasDerivWithinAt
    have hb : ∀ s∈window |t|, |v (p s)-v₀|≤h*|t| := by
      intro s hs
      have hsT : s∈window T := abs_le.mp ((abs_le.mpr hs).trans (abs_le.mpr ht))
      exact (hvr s hsT).trans (mul_le_mul_of_nonneg_left (abs_le.mpr hs) hh)
    convert local_window_bound hder ht hb using 1
    · simp [d₀]
    · ring
  intro t ht
  refine ⟨hdr t ht,?_⟩
  have hder : ∀ s∈window T, HasDerivWithinAt (fun t => y t-(y 0+d₀*t+v₀*t^2/2))
      (d (p s)-(d₀+v₀*s)) (window T) s := by
    intro s hs
    have hp₁ := ((hasDerivAt_id s).const_mul d₀).const_add (y 0)
    have hp₂ := (((hasDerivAt_id s).pow 2).const_mul v₀).div_const 2
    have hpol := (hp₁.add hp₂).hasDerivWithinAt (s:=window T)
    convert (hyd s hs).sub hpol using 1
    norm_num [id_eq]
    ring
  have hb : ∀ s∈window |t|, |d (p s)-(d₀+v₀*s)|≤h*|t|^2 := by
    intro s hs
    have hsT : s∈window T := abs_le.mp ((abs_le.mpr hs).trans (abs_le.mpr ht))
    exact (hdr s hsT).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg s) (abs_le.mpr hs) _) hh)
  convert local_window_bound hder ht hb using 1
  · simp [d₀,v₀,p]
  · ring

def horizontal (p : Plane) (e s : ℝ) : Plane := (p.1+e*s,p.2)

private theorem horizontal_deriv (p : Plane) (e s : ℝ) :
    HasDerivAt (horizontal p e) (e,0) s := by
  simpa [horizontal] using (((hasDerivAt_id s).const_mul e).const_add p.1).prodMk
    (hasDerivAt_const s p.2)

private theorem horizontal_lipschitz (p : Plane) (e T : ℝ) :
    LipschitzPath (horizontal p e) T := by
  refine ⟨⟨|e|,abs_nonneg e⟩,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  simp only [horizontal,Prod.dist_eq,dist_self,Real.dist_eq]
  rw [show p.1+e*x-(p.1+e*y)=e*(x-y) by ring,abs_mul,
    max_eq_left (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
  exact le_rfl

theorem horizontal_correction {E : Set Plane} (hE : IsOpen E) {d : Plane → ℝ}
    {p : Plane} {e M : ℝ} (hM : |e|<M)
    (hb : HasACBuffer E d p M) {h : ℝ}
    (hd : ∀ q∈E, DifferentiableAt ℝ d q)
    (hY : ∀ q∈E, |fderiv ℝ d q (1,0)|≤h) :
    (∀ s∈Icc (0:ℝ) 1, horizontal p e s∈E) ∧
    |d (horizontal p e 1)-d p|≤h*|e| := by
  have hzero : horizontal p e 0=p := by simp [horizontal]
  have hinside : ∀ s∈Icc (0:ℝ) 1, horizontal p e s∈E := by
    intro s hs
    by_contra hnot
    let B : Set ℝ := Icc 0 s ∩ (horizontal p e) ⁻¹' Eᶜ
    have hB : B.Nonempty := ⟨s,⟨⟨hs.1,le_rfl⟩,hnot⟩⟩
    have hcomp : IsCompact B := isCompact_Icc.inter_right
      (hE.isClosed_compl.preimage ((show Differentiable ℝ (horizontal p e) from
        fun t => (horizontal_deriv p e t).differentiableAt).continuous))
    let T := sInf B
    have hTm : T∈B := hcomp.sInf_mem hB
    have hT₀ : 0≤T := hTm.1.1
    have hTs : T≤s := hTm.1.2
    have hfirst : ∀ t∈Ico (0:ℝ) T, horizontal p e t∈E := by
      intro t ht
      by_contra! ht'
      exact (not_le_of_gt ht.2) (csInf_le ⟨0,fun _ h => h.1.1⟩
        (show t∈B from ⟨⟨ht.1,ht.2.le.trans hTs⟩,ht'⟩))
    have hlen : acLength d (horizontal p e) T=ENNReal.ofReal (|e| * T) := by
      have hspeed : ∀ t, coframeSpeed d (horizontal p e) t=|e| := by
        intro t
        rw [coframeSpeed,(horizontal_deriv p e t).deriv]
        simp
      simp only [acLength,hspeed,lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc]
      rw [sub_zero,ENNReal.ofReal_mul (abs_nonneg e)]
    have hh := hb T (horizontal p e) ⟨hT₀,hzero,lipschitz_acPath (horizontal_lipschitz p e T),hfirst,hTm.2⟩
    rw [hlen] at hh
    have hle := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (abs_nonneg e) hT₀)).mp hh
    exact (not_le_of_gt hM) (hle.trans (by nlinarith [mul_le_mul_of_nonneg_left (hTs.trans hs.2) (abs_nonneg e)]))
  refine ⟨hinside,?_⟩
  have hh (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt
      (fun s => d (horizontal p e s)) (e*fderiv ℝ d (horizontal p e t) (1,0)) t := by
    have hc := (hd _ (hinside t ht)).hasFDerivAt.comp_hasDerivAt t (horizontal_deriv p e t)
    rw [show ((e,0):Plane)=e • ((1,0):Plane) by simp,map_smul,smul_eq_mul] at hc
    exact hc
  have hm : ∀ t∈Icc (0:ℝ) 1, ‖derivWithin (fun s => d (horizontal p e s)) (Icc 0 1) t‖≤h*|e| := by
    intro t ht
    rw [(hh t ht).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht),Real.norm_eq_abs,abs_mul,mul_comm]
    exact mul_le_mul_of_nonneg_right (hY _ (hinside t ht)) (abs_nonneg e)
  simpa [hzero] using Convex.norm_image_sub_le_of_norm_derivWithin_le
    (fun t ht => (hh t ht).differentiableAt.differentiableWithinAt) hm
    (convex_Icc (0:ℝ) 1) (by simp : (0:ℝ)∈Icc 0 1) (by simp : (1:ℝ)∈Icc 0 1)

end PaperI.ParabolicCollar
