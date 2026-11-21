import Revision.Span

open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section

namespace PaperI.CollarRevision
open BoundedCharacteristic CorridorBands ShortProjectionCaps CommonNullAssignment ParabolicCollar

/-- The two width hypotheses of Lemma 3.17, including the threshold H=τ.
A is the previously fixed loss bounding m/τ and D is the narrow-width loss. -/
theorem signed_long_width {a b w τ m A D : ℝ} {α : ℝ → ℝ}
    (hτ : 1≤τ) (hH : τ≤b-a) (hm : 0<m) (hA : 1≤A) (hM : m≤A*τ) (hw : 0≤w)
    (hI : IntervalIntegrable α volume a b)
    (h : (w≤D*m ∧ ∀ t∈Ioo a b, 1≤|α t|) ∨
      (∃ C : ℝ, 1≤C ∧ ∀ t∈Ioo a b, max 2 (C*w/m) ≤ |α t|)) :
    let ell := flux α a b
    let L := roundedDyadicScale (max m ell)
    b-a≤ell ∧ 1≤ell ∧ ell≤L ∧ L≤2*A*ell ∧ 2*w≤2*(max A D)*L := by
  intro ell L
  have hab : a≤b := by linarith
  have lower (c : ℝ) (hα : ∀ t∈Ioo a b,c≤|α t|) : c*(b-a)≤ell := by
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo hab
      (continuous_const.intervalIntegrable a b : IntervalIntegrable (fun _ : ℝ => c) volume a b)
      hI.abs hα
    simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm,ell,flux] using hh
  have h1 : ∀ t∈Ioo a b, 1≤|α t| := by
    rcases h with hn|⟨C,_,hh⟩
    · exact hn.2
    · exact fun t ht => (show (1:ℝ)≤2 by norm_num).trans ((le_max_left ..).trans (hh t ht))
  have hlen : b-a≤ell := by simpa using lower 1 h1
  have he : 1≤ell := hτ.trans (hH.trans hlen)
  have hL : max m ell≤L := le_roundedDyadicScale _
  have hmL := (le_max_left m ell).trans hL
  have heL := (le_max_right m ell).trans hL
  have hMax : max m ell≤A*ell := max_le (hM.trans (mul_le_mul_of_nonneg_left (hH.trans hlen) (by linarith)))
    (le_mul_of_one_le_left (by linarith) hA)
  have hL' := (roundedDyadicScale_lt_two_max (max m ell)).le
  rw [max_eq_right (he.trans (le_max_right ..))] at hL'
  refine ⟨hlen,he,heL,by change roundedDyadicScale (max m ell)≤_; linarith,?_⟩
  have hcoef : 0≤max A D := (show 0≤A by linarith).trans (le_max_left ..)
  suffices hh : w≤max A D*L by linarith
  rcases h with hn|⟨C,hC,hh⟩
  · exact hn.1.trans ((mul_le_mul_of_nonneg_right (le_max_right ..) hm.le).trans (mul_le_mul_of_nonneg_left hmL hcoef))
  · have hc : w/m≤C*w/m := div_le_div_of_nonneg_right (le_mul_of_one_le_left hw hC) hm.le
    have hc' := lower (w/m) (fun t ht => hc.trans ((le_max_right ..).trans (hh t ht)))
    have hh' : w*(b-a)≤ell*m := by
      have heq : w/m*(b-a) = (w*(b-a))/m := by ring
      rw [heq] at hc'
      exact (div_le_iff₀ hm).mp hc'
    have hm' : m≤A*(b-a) := hM.trans (mul_le_mul_of_nonneg_left hH (by linarith))
    have ht : w*(b-a) ≤ (A*ell)*(b-a) := hh'.trans ((mul_le_mul_of_nonneg_left hm' (by linarith)).trans_eq (by ring))
    have hwe := le_of_mul_le_mul_right ht (show 0<b-a by linarith)
    exact hwe.trans (mul_le_mul (le_max_left ..) heL (by linarith) hcoef)

/-- The polynomial cost of the full horizontal segment controls the original slope and path. -/
theorem horizontal_bridge {E : Set Plane} {d : Plane → ℝ} {p : Plane} {y M L R : ℝ}
    (hL : 0<L) (hR : 0<R) (hM : 0≤M) (hWidth : |y-p.1|≤R*L)
    (hIn : ∀ x∈uIcc p.1 y, (x,p.2)∈E)
    (hSlope : ∀ x∈uIcc p.1 y, DifferentiableAt ℝ d (x,p.2) ∧ |fderiv ℝ d (x,p.2) (1,0)|≤M) :
    |d (y,p.2)-d p|≤M*(R*L) ∧ IntrinsicReach E d p (y,p.2) (3*(R*L)) := by
  have hd (x : ℝ) (hx : x∈uIcc p.1 y) := (hSlope x hx).1.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x p.2))
  have hDiff := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x hx).hasDerivWithinAt) (fun x hx => (hSlope x hx).2)
    (convex_Icc _ _) (left_mem_uIcc (a:=p.1) (b:=y)) (right_mem_uIcc (a:=p.1) (b:=y))
  refine ⟨hDiff.trans (mul_le_mul_of_nonneg_left hWidth hM),?_⟩
  apply actual_horizontal_path (p:=p) (q:=(y,p.2)) rfl (hWidth.trans_lt (by linarith [mul_pos hR hL]))
  intro t ht
  have hi := convex_Icc (min p.1 y) (max p.1 y) (left_mem_uIcc (a:=p.1) (b:=y))
    (right_mem_uIcc (a:=p.1) (b:=y)) (by linarith [ht.2] : 0≤1-t) ht.1 (show (1-t)+t=1 by ring)
  apply hIn
  convert hi using 1
  simp [horizontal,smul_eq_mul]
  ring

theorem short_corridor_span {P m τ M δ Λ : ℝ} {C Cf K k H sf df n : ℕ}
    {ι : Type} [DecidableEq ι] {E A Ω : Set Plane} {d v : Plane → ℝ} {keep : Plane → Prop}
    {F : Plane → ℝ → ℝ} {labels : Finset ι} {rep : ι → Plane} {frame : Plane → Fin 6 → ℝ}
    (cap : PhaseCap P m τ Λ K k Cf H sf df n E Ω d v keep F labels rep)
    (hP : 2≤P) (hm : 1≤m) (hτ : 0<τ) (hτm : τ≤m) (hM : 4*m<M)
    (hδ : 0≤δ) (hs : P^C*δ*(2*m)≤Real.log 2)
    (hd : ∀ p∈E,ContDiffAt ℝ 1 d p) (box : ∀ p∈A,CertifiedBox P δ M C Cf E d v frame p)
    (hSub : Ω⊆A) (hBound : ∃ R,∀ q∈E, |q.1|≤R ∧ |q.2|≤R)
    {a b w : ℝ} {Γ : ℝ → ℝ} (hab : a<b) (mid : ∀ z∈Ioo a b,(Γ z,z)∈Ω)
    (sec : ∀ q∈Ω, q.2∈Ioo a b ∧ |q.1-Γ q.2|≤2*w ∧ ∀ y∈uIcc (Γ q.2) q.1,(y,q.2)∈Ω)
    (hΓ : ContDiffOn ℝ ∞ Γ (Ioo a b)) (hi : IntervalIntegrable (transverseResidual Γ d) volume a b) :
    let I := project Ω F '' Ω
    let α := transverseResidual Γ d
    horizontalSpan I≤8*w+2*flux α a b ∧
      ((∀ z∈Ioo a b,0≤α z) ∨ (∀ z∈Ioo a b,α z≤0) → flux α a b/2≤horizontalSpan I ∧
        flux α a b/2≤horizontalSpan ((fun z => project Ω F (Γ z,z)) '' Ioo a b)) := by
  have hcont : ContinuousOn (transverseResidual Γ d) (Ioo a b) := by
    have hdE : ContinuousOn d E := fun p hp => (hd p hp).continuousAt.continuousWithinAt
    have hMap : MapsTo (fun z => (Γ z,z)) (Ioo a b) E := by
      intro z hz
      let B := box (Γ z,z) (hSub (mid z hz))
      exact B.carrier_subset B.mem_carrier
    have hCurve : ContinuousOn (fun z => (Γ z,z)) (Ioo a b) := hΓ.continuousOn.prodMk continuousOn_id
    have hΓ' : ContDiffOn ℝ ∞ (deriv Γ) (Ioo a b) := hΓ.deriv_of_isOpen isOpen_Ioo (by simp)
    exact hΓ'.continuousOn.sub (hdE.comp hCurve hMap)
  obtain ⟨hLo,hHi⟩ := projection_bounded cap hτ hBound
  exact projected_graph_span hab mid sec (hΓ.differentiableOn (by simp)) hcont hi
    (cap_projection_derivative cap hP hm hτ hτm hM hδ hs hd box hSub) hLo hHi

end PaperI.CollarRevision
