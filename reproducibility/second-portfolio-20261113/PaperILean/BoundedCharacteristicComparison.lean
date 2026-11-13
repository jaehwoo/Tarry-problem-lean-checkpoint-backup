import PaperILean.BoundedCharacteristicBuffer
import PaperILean.BoundedCharacteristicTube
import PaperILean.OriginalGaussRelativeFrameIntegration

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal Matrix.L2OpNorm

noncomputable section

namespace PaperI.BoundedCharacteristic

private theorem signed_trajectory {D : Set Plane} (hD : IsOpen D) {d v : Plane → ℝ}
    (hd : ∀ p ∈ D, ContDiffAt ℝ 1 d p)
    (hv : ∀ p ∈ D, fderiv ℝ d p (d p,1)=v p)
    {V z T y₀ M : ℝ} (hV : ∀ p ∈ D, |v p|≤V) (hT : 0<T) (hTM : T<M)
    (hp : (y₀,z)∈D) (hbuffer : HasACBuffer D d (y₀,z) M) :
    ∃ y : ℝ → ℝ, y 0=y₀ ∧ DirectedSolution D d z 1 (-T) T y := by
  obtain ⟨ypos,hyp0,hyp⟩ := source_directed_continuation hD hd hv hV
    (σ:=1) (by norm_num) hT hTM hp hbuffer
  obtain ⟨yneg,hyn0,hyn⟩ := source_directed_continuation hD hd hv hV
    (σ:=-1) (by norm_num) hT hTM hp hbuffer
  let yneg' := fun t => yneg (-t)
  have hneg : DirectedSolution D d z 1 (-T) 0 yneg' := by
    intro t ht
    have ht' : -t ∈ Icc (0:ℝ) T := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have he : directedPoint z 1 yneg' t=directedPoint z (-1) yneg (-t) := by
      simp [directedPoint,yneg']
    rw [he]
    refine ⟨(hyn _ ht').1,?_⟩
    have hder := (hyn _ ht').2.scomp t
      ((hasDerivAt_id t).neg.hasDerivWithinAt (s:=Icc (-T) 0))
      (show MapsTo (fun t : ℝ => -id t) (Icc (-T) 0) (Icc 0 T) from fun x hx =>
        ⟨by simpa using neg_nonneg.mpr hx.2,by simp; linarith [hx.1]⟩)
    simpa [Function.comp_def,yneg'] using hder
  let y := fun t => if t≤0 then yneg' t else ypos t
  have hy0 : y 0=y₀ := by simp [y,yneg',hyn0]
  have hjoined := join_directed_solution (neg_nonpos.mpr hT.le) hT.le hneg hyp
    (by simp [yneg',hyn0,hyp0])
  exact ⟨y,hy0,hjoined⟩

private theorem signed_residual_buffer
    {D : Set Plane} {d : Plane → ℝ} {z T y₀ M : ℝ}
    {V : ℝ} (hT : 0<T) (hd : ∀ p∈D, ContDiffAt ℝ 1 d p)
    (hV : ∀ p∈D, |fderiv ℝ d p (d p,1)|≤V)
    {y : ℝ → ℝ} (hy0 : y 0=y₀)
    (hy : DirectedSolution D d z 1 (-T) T y) (hb : HasACBuffer D d (y₀,z) M)
    {t : ℝ} (ht : t∈window T) :
    HasACBuffer D d (point y z t) (M-|t|) := by
  have habs : |t|≤T := abs_le.mpr ht
  let σ := if 0≤t then (1:ℝ) else -1
  have hσ : |σ|=1 := by by_cases h : 0≤t <;> simp [σ,h]
  have hσt : σ*|t|=t := by
    by_cases h : 0≤t
    · simp [σ,h,abs_of_nonneg h]
    · simp [σ,h,abs_of_neg (lt_of_not_ge h)]
  let f := fun s => y (σ*s)
  have hmap : MapsTo (fun s => σ*s) (Icc (0:ℝ) |t|) (Icc (-T) T) := by
    intro s hs
    apply abs_le.mp
    rw [abs_mul,hσ,one_mul,abs_of_nonneg hs.1]
    exact hs.2.trans habs
  have hf : DirectedSolution D d z σ 0 |t| f := by
    intro s hs
    have h := hy (σ*s) (hmap hs)
    have hp : directedPoint z σ f s=directedPoint z 1 y (σ*s) := by
      simp [directedPoint,f]
    rw [hp]
    refine ⟨h.1,?_⟩
    have hd := h.2.scomp s (((hasDerivAt_id s).const_mul σ).hasDerivWithinAt
      (s:=Icc (0:ℝ) |t|)) hmap
    simpa [Function.comp_def,f] using hd
  have hf0 : directedPoint z σ f 0=(y₀,z) := by simp [directedPoint,f,hy0]
  have hfend : directedPoint z σ f |t|=point y z t := by simp [directedPoint,f,point,hσt]
  have hLip : LipschitzPath (directedPoint z σ f) |t| := by
    rcases eq_or_lt_of_le (abs_nonneg t) with h0 | hp
    · rw [←h0]
      exact ⟨0,LipschitzOnWith.of_dist_le_mul (by
        intro s hs r hr
        have hs' : s=0 := le_antisymm hs.2 hs.1
        have hr' : r=0 := le_antisymm hr.2 hr.1
        simp [hs',hr'])⟩
    · have hV0 : 0≤V := (abs_nonneg _).trans (hV _ (hf 0 ⟨le_rfl,hp.le⟩).1)
      have hf0' : f 0=y₀ := by simp [f,hy0]
      let K : ℝ≥0 := ⟨|d (y₀,z)|+V*T,by positivity⟩
      apply directedPoint_lipschitz (K:=K) hσ
      apply LipschitzOnWith.of_dist_le_mul
      intro s hs r hr
      rw [Real.dist_eq,Real.dist_eq]
      exact solution_value_lipschitz hd (fun _ _ => rfl) hV hσ hp habs hf0' hf s hs r hr
  rw [← hfend]
  exact source_buffer_after_directed (abs_nonneg _) hσ hf hLip (hf0 ▸ hb)

/-- The literal relative homogeneous affine matrix of the actual selected
frames in the original six-coordinate convention. -/
def relativeFrameNorm (frame : Plane → Fin 6 → ℝ) (p q : Plane) : ℝ :=
  ‖originalAffineHomogeneousMatrix (originalUpperRelativeFrame (frame p) (frame q))‖

private theorem slope_horizontal {d : Plane → ℝ} {D : Set Plane}
    (hd : ∀ p∈D, ContDiffAt ℝ 1 d p) {p : Plane} (hp : p∈D) :
    HasDerivAt (fun x => d (x,p.2)) (fderiv ℝ d p (1,0)) p.1 := by
  have hfun : HasDerivAt (fun x : ℝ => (x,p.2)) ((1,0):Plane) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const _ _)
  have hd' := ((hd p hp).differentiableAt (by norm_num)).hasFDerivAt
  simpa [Function.comp_def] using hd'.comp_hasDerivAt p.1 hfun

private theorem horizontalRate_continuous {D : Set Plane} (hD : IsOpen D)
    {d : Plane → ℝ} (hd : ∀ p∈D, ContDiffAt ℝ 1 d p) :
    ContinuousOn (fun p => fderiv ℝ d p ((1,0):Plane)) D := by
  have hc : ContDiffOn ℝ 1 d D := fun p hp => (hd p hp).contDiffWithinAt
  have hdf := hc.continuousOn_fderiv_of_isOpen hD (by norm_num)
  exact hdf.clm_apply continuousOn_const

/-- Paper I I961–I966, proof I967–I969. The outer box is the original
certified box in the continued branch, not a smaller artificial cell.
No neighboring flow, transverse derivative, continuation, or residual
buffer is assumed. The buffer quantifies all AC first exits. -/
theorem bounded_time_characteristic_comparison
    {P m₀ δ : ℝ} (hP : 2≤P) (hm : 1≤m₀) (hδ : 0≤δ)
    (C : ℕ) (D : Set Plane) (hD : IsOpen D)
    (d : Plane → ℝ) (hregular : ∀ p∈D, ContDiffAt ℝ 1 d p)
    (retained : Plane → Prop) (hretain : ∀ p∈D, retained p)
    (frame : Plane → Fin 6 → ℝ) (frameExponent : ℕ)
    (hcompare : ∀ p∈D, ∀ q∈D, relativeFrameNorm frame p q ≤ P^frameExponent)
    (hsmall : (P^C*δ)*(2*m₀)≤Real.log 2)
    (hrate : ∀ p∈D,
      |fderiv ℝ d p ((1,0):Plane)|≤P^C*δ ∧
      |fderiv ℝ d p (d p,1)|≤P^C) :
    let T := 2*m₀
    let u := fun p : Plane => fderiv ℝ d p ((1,0):Plane)
    (∀ z y, DirectedSolution D d z 1 (-T) T y →
      ∃ F : ℝ → ℝ → ℝ, ∃ r > 0, F (y 0)=y ∧
        (∀ x, |x-y 0|<r → F x 0=x ∧ DirectedSolution D d z 1 (-T) T (F x)) ∧
        (∀ t∈window T,
          let J := Real.exp (∫ s in (0:ℝ)..t, u (point y z s))
          HasDerivAt (fun x => F x t) J (y 0) ∧
          HasDerivWithinAt (fun t => Real.exp (∫ s in (0:ℝ)..t, u (point y z s)))
            (u (point y z t)*J) (window T) t ∧
          1/2≤J ∧ J≤2 ∧ 1/2≤J⁻¹ ∧ J⁻¹≤2 ∧
          retained (point y z t) ∧
          relativeFrameNorm frame (point y z 0) (point y z t) ≤ P^frameExponent)) ∧
    (∀ y₀ z M, (y₀,z)∈D → 4*m₀<M → HasACBuffer D d (y₀,z) M →
      ∃ y : ℝ → ℝ, y 0=y₀ ∧ DirectedSolution D d z 1 (-T) T y ∧
        (∀ t∈window T, HasACBuffer D d (point y z t) (M-|t|) ∧
          HasACBuffer D d (point y z t) (M-T))) := by
  dsimp only
  have hT : (0:ℝ)<2*m₀ := by linarith
  have hL : 0≤P^C*δ := mul_nonneg (pow_nonneg (by linarith) _) hδ
  have hd : ContinuousOn d D := fun p hp =>
    (hregular p hp).continuousAt.continuousWithinAt
  have hu := horizontalRate_continuous hD hregular
  have hud := fun p hp => slope_horizontal hregular (p:=p) hp
  constructor
  · intro z y hy
    have hpoint : ∀ t∈window (2*m₀), point y z t∈D := fun t ht => by
      simpa [point,directedPoint] using (hy t ht).1
    have hy' : ∀ t∈window (2*m₀),
        HasDerivWithinAt y (d (point y z t)) (window (2*m₀)) t := fun t ht => by
      simpa [point,directedPoint] using (hy t ht).2
    obtain ⟨F,r,hr,hF,hFlows,hDeriv⟩ :=
      actual_transverse_derivative hT hL hsmall hD hd hu hud
        (fun p hp => (hrate p hp).1) hpoint hy'
    refine ⟨F,r,hr,hF,?_,?_⟩
    · intro x hx
      obtain ⟨hx0,hxFlow⟩ := hFlows x hx
      refine ⟨hx0,fun t ht => ?_⟩
      simpa [point,directedPoint] using hxFlow t ht
    · intro t ht
      have hyc : ContinuousOn y (window (2*m₀)) := fun t ht => (hy' t ht).continuousWithinAt
      have hpc : ContinuousOn (point y z) (window (2*m₀)) := hyc.prodMk (by fun_prop)
      have huc := hu.comp hpc hpoint
      have h0 : (0:ℝ)∈window (2*m₀) := ⟨by linarith,hT.le⟩
      obtain ⟨h₁,h₂,h₃,h₄⟩ := exponential_bounds hT.le hL hsmall
        (fun s hs => (hrate _ (hpoint s hs)).1) ht
      exact ⟨hDeriv t ht,exponential_derivative_window hT.le huc ht,h₁,h₂,h₃,h₄,
        hretain _ (hpoint t ht),hcompare _ (hpoint 0 h0) _ (hpoint t ht)⟩
  · intro y₀ z M hp hM hb
    obtain ⟨y,hy0,hy⟩ := signed_trajectory hD hregular
      (v:=fun p => fderiv ℝ d p (d p,1)) (fun _ _ => rfl)
      (fun p hp => (hrate p hp).2) hT (by linarith) hp hb
    refine ⟨y,hy0,hy,fun t ht => ?_⟩
    have hres := signed_residual_buffer hT hregular (fun p hp => (hrate p hp).2) hy0 hy hb ht
    exact ⟨hres,fun b γ hγ =>
      (ENNReal.ofReal_le_ofReal (sub_le_sub_left (abs_le.mpr ht) _)).trans (hres b γ hγ)⟩

end PaperI.BoundedCharacteristic
