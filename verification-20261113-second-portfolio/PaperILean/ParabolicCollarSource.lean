import PaperILean.ParabolicCollarWhole

open Set MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace PaperI.ParabolicCollar
open BoundedCharacteristic

private theorem acPath_continuousOn {γ : ℝ → Plane} {T : ℝ}
    (hT : 0≤T) (h : ACPath γ T) : ContinuousOn γ (Icc 0 T) := by
  obtain ⟨g,hg,_,hh⟩ := h
  let F := fun t : ℝ => ∫ r in (0:ℝ)..t, g r
  have hF : ContinuousOn F (Icc 0 T) := by
    rw [← uIcc_of_le hT]
    apply intervalIntegral.continuousOn_primitive_interval
    rw [uIcc_of_le hT]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hg
  have hFdiff {a b : ℝ} (ha : a∈Icc 0 T) (hb : b∈Icc 0 T) :
      F b-F a = ∫ r in a..b, g r := by
    have h₁ : IntervalIntegrable g volume 0 a := hg.mono_set (by
      rw [uIcc_of_le ha.1,uIcc_of_le hT]
      exact Icc_subset_Icc_right ha.2)
    have h₂ : IntervalIntegrable g volume a b := hg.mono_set (by
      rw [uIcc_of_le hT]
      exact uIcc_subset_Icc ha hb)
    have he := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
    change F a + (∫ r in a..b, g r) = F b at he
    linarith
  have hdist {a b : ℝ} (ha : a∈Icc 0 T) (hb : b∈Icc 0 T) :
      dist (γ a) (γ b) ≤ dist (F a) (F b) := by
    rw [Real.dist_eq]
    rcases le_total a b with hab | hba
    · rw [abs_sub_comm]
      exact (hh a ha b hb hab).trans (by rw [← hFdiff ha hb]; exact le_abs_self _)
    · rw [dist_comm (γ a)]
      exact (hh b hb a ha hba).trans (by rw [← hFdiff hb ha]; exact le_abs_self _)
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  obtain ⟨r,hr,hnear⟩ := Metric.continuousOn_iff.mp hF x hx ε hε
  exact ⟨r,hr,fun y hy hyx => (hdist hy hx).trans_lt (hnear y hy hyx)⟩

private theorem acPath_restrict {γ : ℝ → Plane} {T b : ℝ} (hb : 0≤b) (hbT : b≤T)
    (h : ACPath γ T) : ACPath γ b := by
  obtain ⟨g,hg,hg₀,hh⟩ := h
  have hsub : Icc (0:ℝ) b ⊆ Icc 0 T := Icc_subset_Icc_right hbT
  refine ⟨g,hg.mono_set ?_,hg₀,fun x hx y hy hxy => hh x (hsub hx) y (hsub hy) hxy⟩
  rwa [uIcc_of_le hb,uIcc_of_le (hb.trans hbT)]

private theorem ac_buffer_mono {D E : Set Plane} {d : Plane → ℝ} {p : Plane} {M : ℝ}
    (hD : IsOpen D) (hsub : D⊆E) (hbuf : HasACBuffer D d p M) : HasACBuffer E d p M := by
  intro T γ hγ
  obtain ⟨hT,hzero,hac,_,hex⟩ := hγ
  let B : Set ℝ := Icc 0 T ∩ γ ⁻¹' Dᶜ
  have hB : B.Nonempty := ⟨T,⟨⟨hT,le_rfl⟩,fun h => hex (hsub h)⟩⟩
  have hclosed : IsClosed B := (acPath_continuousOn hT hac).preimage_isClosed_of_isClosed
    isClosed_Icc hD.isClosed_compl
  have hcompact : IsCompact B := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  let b := sInf B
  have hb : b∈B := hcompact.sInf_mem hB
  have hfirst : ∀ t∈Ico 0 b, γ t∈D := by
    intro t ht
    by_contra hnot
    exact (not_le_of_gt ht.2) (csInf_le ⟨0,fun _ hz => hz.1.1⟩
      (show t∈B from ⟨⟨ht.1,ht.2.le.trans hb.1.2⟩,hnot⟩))
  have hlength := hbuf b γ ⟨hb.1.1,hzero,acPath_restrict hb.1.1 hb.1.2 hac,hfirst,hb.2⟩
  exact hlength.trans (lintegral_mono_set (Ioc_subset_Ioc_right hb.1.2))

private theorem const_frame_compare {P : ℝ} (hP : 2≤P) :
    ∃ C : ℕ, ∀ p q : Plane, relativeFrameNorm (fun _ _ => 0) p q≤P^C := by
  have htwo (C : ℕ) : C ≤ 2^C := by
    induction C with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      have hp : 0 < 2^n := by positivity
      omega
  obtain ⟨C,hC⟩ := exists_nat_ge (relativeFrameNorm (fun _ _ => 0) (0,0) (0,0))
  have htwo' : (C:ℝ) ≤ (2:ℝ)^C := by exact_mod_cast htwo C
  refine ⟨C,fun p q => ?_⟩
  change relativeFrameNorm (fun _ _ => 0) (0,0) (0,0) ≤ _
  exact hC.trans (htwo'.trans (pow_le_pow_left₀ (by norm_num) hP _))

/-- Source-facing version of I980–I993 with the supplied local model box
chosen separately at each seed parameter. The union is only used inside
the proof, and the output is contained in the full outer admissible set. -/
theorem parabolic_collars_local_boxes
    (hQQE : PublishedQuantitativeRealQE) (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality) (hQE : PublishedRealSemialgebraicity)
    (s D K : ℕ) :
    ∃ sOut DOut N : ℕ,
      ∀ {P m δ c M : ℝ}, 2≤P → 1≤m → 0≤δ → 0<c → c≤1 → (P^K)⁻¹≤c → 4*m<M →
      ∀ C : ℕ, (P^C*δ)*m^3≤1/16 →
      ∀ (E : Set Plane) (d v : Plane → ℝ) (retained : Plane → Prop),
      (∀ p∈E, retained p) →
      ∀ (a b a' b' : ℝ), a≤b → ∀ (γ γ' : ℝ → Plane) (A ν r : ℝ → ℝ),
      ContinuousOn r (Ioo a' b') → BijOn r (Ioo a' b') (Ioo a b) →
      (∀ z∈Ioo a' b', γ (r z)=γ' z) →
      ∀ (box : ℝ → Set Plane),
      (∀ z∈Ioo a b, IsOpen (box z) ∧ box z⊆E ∧ γ z∈box z ∧ HasACBuffer (box z) d (γ z) M ∧
        (∀ p∈box z, ContDiffAt ℝ 1 d p ∧ DifferentiableAt ℝ v p ∧ fderiv ℝ d p (d p,1)=v p ∧
          |fderiv ℝ d p (1,0)|≤P^C*δ ∧ |fderiv ℝ v p (1,0)|≤P^C*δ ∧
          |fderiv ℝ v p (d p,1)|≤P^C*δ ∧ |v p|≤P^C) ∧
        HasDerivAt (fun t => (γ t).1) (A z) z ∧ HasDerivAt (fun t => (γ t).2) (ν z) z ∧
        A z-d (γ z)*ν z=1 ∧ |ν z|≤1) →
      ∀ B : Finset (MvPolynomial (Unit ⊕ Fin 4) ℝ), B.card≤s →
      (∀ p∈B,p.totalDegree≤D) → PolynomialSignDetermined B (originalSeedGraph a' b' γ' d v) →
      let Ω := fluxRectangle a b (c*m)
      let Ψ := collarMap γ d v
      (∀ x∈Ω,
        let p := γ (x 0)
        let Jd := fderiv ℝ d p (1,0)
        let V' := fderiv ℝ v p (1,0)+ν (x 0)*fderiv ℝ v p (d p,1)
        let L := matrixMap (collarJac (A (x 0)) (ν (x 0)) (d p) (v p)
          (Jd+ν (x 0)*v p) V' (x 1))
        let Cₜ := d p+v p*x 1-d (collarPoint γ d v x)
        let U := coframeMatrix L.det (ν (x 0)) Cₜ
        let V := inverseCoframe L.det (ν (x 0)) Cₜ
        collarPoint γ d v x∈E ∧ retained (collarPoint γ d v x) ∧
          HasFDerivAt Ψ L x ∧ L.det=1+Jd*x 1+V'*(x 1)^2/2 ∧
          (thetaMap (d (collarPoint γ d v x))).comp L=matrixMap U ∧
          U*V=1 ∧ V*U=1 ∧ ‖matrixMap U‖≤P^(4+K+N) ∧ ‖matrixMap V‖≤P^(4+K+N)) ∧
      (∀ y, Finite {x | x∈Ω ∧ Ψ x=y} ∧ Nat.card {x | x∈Ω ∧ Ψ x=y}≤N) ∧
      MeasurableSet (Ψ '' Ω) ∧
      (P^(4+K+N))⁻¹*m*(b-a)≤volume.real (Ψ '' Ω) ∧
      volume.real (Ψ '' Ω)≤P^(4+K+N)*m*(b-a) ∧
      ∃ B' : Finset (MvPolynomial (Fin 2 ⊕ Fin 2) ℝ), B'.card≤sOut ∧
        (∀ p∈B',p.totalDegree≤DOut) ∧
        PolynomialSignDetermined B' (originalCollarGraph a' b' (c*m) γ' d v) := by
  obtain ⟨sOut,DOut,N,h⟩ := parabolic_collars hQQE hCell hHardt hQE s D K
  refine ⟨sOut,DOut,N,?_⟩
  intro P m δ c M hP hm hδ hc hc₁ hcL hM C hsmall E d v retained hretained
    a b a' b' hab γ γ' A ν r hr hb hγ box hbox B hBc hBd hB
  let O : Set Plane := ⋃ z : Ioo a b, box z.val
  have hO : IsOpen O := isOpen_iUnion (fun z => (hbox z.val z.property).1)
  have hsub : O⊆E := iUnion_subset (fun z => (hbox z.val z.property).2.1)
  have hdata (p : Plane) (hp : p∈O) :
      ContDiffAt ℝ 1 d p ∧ DifferentiableAt ℝ v p ∧ fderiv ℝ d p (d p,1)=v p ∧
      |fderiv ℝ d p (1,0)|≤P^C*δ ∧ |fderiv ℝ v p (1,0)|≤P^C*δ ∧
      |fderiv ℝ v p (d p,1)|≤P^C*δ ∧ |v p|≤P^C := by
    obtain ⟨z,hz⟩ := mem_iUnion.mp hp
    exact (hbox z.val z.property).2.2.2.2.1 p hz
  have hseed (z : ℝ) (hz : z∈Ioo a b) : γ z∈O ∧ HasACBuffer O d (γ z) M ∧
      HasDerivAt (fun t => (γ t).1) (A z) z ∧ HasDerivAt (fun t => (γ t).2) (ν z) z ∧
      A z-d (γ z)*ν z=1 ∧ |ν z|≤1 := by
    obtain ⟨ho,_,hp,hh,_,ha,hb,hu,hv⟩ := hbox z hz
    have hs : box z⊆O := subset_iUnion (fun t : Ioo a b => box t.val) ⟨z,hz⟩
    exact ⟨hs hp,ac_buffer_mono ho hs hh,ha,hb,hu,hv⟩
  obtain ⟨Cframe,hframe⟩ := const_frame_compare hP
  obtain ⟨hgeometry,hrest⟩ := h hP hm hδ hc hc₁ hcL hM C hsmall hO d v
    (fun p hp => (hdata p hp).1) (fun p hp => (hdata p hp).2.1) (fun p hp => (hdata p hp).2.2.1)
    (fun p hp => (hdata p hp).2.2.2) retained (fun p hp => hretained p (hsub hp))
    (fun _ _ => 0) Cframe (fun p _ q _ => hframe p q)
    a b a' b' hab γ γ' A ν r hr hb hγ hseed B hBc hBd hB
  refine ⟨?_,hrest⟩
  intro x hx
  exact ⟨hsub (hgeometry x hx).1,(hgeometry x hx).2⟩

end PaperI.ParabolicCollar
