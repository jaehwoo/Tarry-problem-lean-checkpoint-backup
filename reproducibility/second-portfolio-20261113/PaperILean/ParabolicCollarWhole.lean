import PaperILean.ParabolicCollarCoframe
import PaperILean.ParabolicCollarFormat
import PaperILean.ParabolicCollarArea

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace PaperI.ParabolicCollar
open BoundedCharacteristic

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp : 0<2^n := by positivity
    omega

private theorem collar_area_powers {Q : Set Coordinates} {P m c a b : ℝ} {K N : ℕ}
    (hP : 2≤P) (hm : 0≤m) (hc : 0<c) (hc₁ : c≤1) (hab : a≤b)
    (hcL : (P^K)⁻¹≤c)
    (hl : ENNReal.ofReal (2*(c*m)*(b-a)) ≤ (2*(N:ℝ≥0∞))*volume Q)
    (hu : volume Q ≤ ENNReal.ofReal (3*(c*m)*(b-a))) :
    (P^(4+K+N))⁻¹*m*(b-a) ≤ volume.real Q ∧ volume.real Q ≤ P^(4+K+N)*m*(b-a) := by
  have hP₁ : 1≤P := by linarith
  have hP₀ : 0<P := by linarith
  have hL : 0≤b-a := sub_nonneg.mpr hab
  have h₀ : 0≤m*(b-a) := mul_nonneg hm hL
  have hQfin : volume Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have hcoeff : (2*(N:ℝ≥0∞))≠⊤ := ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top N)
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hcoeff hQfin) hl
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  change (ENNReal.ofReal _).toReal ≤ _ at h1
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*(c*m)*(b-a)),ENNReal.toReal_mul,
    ENNReal.toReal_natCast,ENNReal.toReal_ofNat] at h1
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 3*(c*m)*(b-a))] at h2
  have hN₂ : (N:ℝ)≤(2:ℝ)^N := by exact_mod_cast nat_le_two_pow N
  have hNP : (N:ℝ)≤P^N := hN₂.trans (pow_le_pow_left₀ (by norm_num) hP N)
  have hN₀ : 0≤(volume Q).toReal := ENNReal.toReal_nonneg
  have htmp : (P^K)⁻¹*(m*(b-a)) ≤ P^N*(volume Q).toReal := calc
    (P^K)⁻¹*(m*(b-a)) ≤ c*(m*(b-a)) := mul_le_mul_of_nonneg_right hcL h₀
    _ ≤ (N:ℝ)*(volume Q).toReal := by linarith only [h1]
    _ ≤ P^N*(volume Q).toReal := mul_le_mul_of_nonneg_right hNP hN₀
  have hPN : 0 < P^N := pow_pos hP₀ _
  have hl' : ((P^(4+K+N))⁻¹*m)*(b-a)≤(volume Q).toReal := by
    have hmon : (P^(4+K+N))⁻¹*(m*(b-a))≤(P^N)⁻¹*((P^K)⁻¹*(m*(b-a))) := by
      calc
        (P^(4+K+N))⁻¹*(m*(b-a)) ≤ (P^(K+N))⁻¹*(m*(b-a)) := by
          have hb : P^(K+N)≤P^(4+K+N) := pow_le_pow_right₀ hP₁ (by omega)
          exact mul_le_mul_of_nonneg_right (inv_anti₀ (pow_pos hP₀ _) hb) h₀
        _ = _ := by
          rw [pow_add,mul_inv_rev]
          ring
    rw [mul_assoc]
    refine hmon.trans ?_
    calc
      (P^N)⁻¹*((P^K)⁻¹*(m*(b-a))) ≤ (P^N)⁻¹*(P^N*(volume Q).toReal) :=
        mul_le_mul_of_nonneg_left htmp (inv_nonneg.mpr hPN.le)
      _ = _ := by rw [←mul_assoc,inv_mul_cancel₀ hPN.ne',one_mul]
  have h3 : (3:ℝ) ≤ P^(4+K+N) := calc
    3 ≤ (2:ℝ)^4 := by norm_num
    _ ≤ P^4 := pow_le_pow_left₀ (by norm_num) hP _
    _ ≤ _ := pow_le_pow_right₀ hP₁ (by omega)
  refine ⟨hl',h2.trans ?_⟩
  calc
    3*(c*m)*(b-a) = (3*c)*(m*(b-a)) := by ring
    _ ≤ (3:ℝ)*(m*(b-a)) := mul_le_mul_of_nonneg_right (by linarith) h₀
    _ ≤ P^(4+K+N)*(m*(b-a)) := mul_le_mul_of_nonneg_right h3 h₀
    _ = _ := by ring

/-- Whole Paper I I980–I993. The open intervals are the flux and original
seed parameter interiors. The four-valued original seed graph comprises the
actual coordinates and the original slope and slope rate in I1017. -/
theorem parabolic_collars
    (hQQE : PublishedQuantitativeRealQE) (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality) (hQE : PublishedRealSemialgebraicity)
    (s D K : ℕ) :
    ∃ sOut DOut N : ℕ,
      ∀ {P m δ c M : ℝ}, 2≤P → 1≤m → 0≤δ → 0<c → c≤1 → (P^K)⁻¹≤c → 4*m<M →
      ∀ C : ℕ, (P^C*δ)*m^3≤1/16 →
      ∀ {E : Set Plane}, IsOpen E → ∀ (d v : Plane → ℝ),
      (∀ p∈E, ContDiffAt ℝ 1 d p) → (∀ p∈E, DifferentiableAt ℝ v p) →
      (∀ p∈E, fderiv ℝ d p (d p,1)=v p) →
      (∀ p∈E, |fderiv ℝ d p (1,0)|≤P^C*δ ∧ |fderiv ℝ v p (1,0)|≤P^C*δ ∧
        |fderiv ℝ v p (d p,1)|≤P^C*δ ∧ |v p|≤P^C) →
      ∀ (retained : Plane → Prop), (∀ p∈E, retained p) →
      ∀ (frame : Plane → Fin 6 → ℝ) (Cframe : ℕ),
      (∀ p∈E, ∀ q∈E, relativeFrameNorm frame p q≤P^Cframe) →
      ∀ (a b a' b' : ℝ), a≤b → ∀ (γ γ' : ℝ → Plane) (A ν r : ℝ → ℝ),
      ContinuousOn r (Ioo a' b') → BijOn r (Ioo a' b') (Ioo a b) →
      (∀ z∈Ioo a' b', γ (r z)=γ' z) →
      (∀ z∈Ioo a b, γ z∈E ∧ HasACBuffer E d (γ z) M ∧
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
  obtain ⟨sOut,DOut,hformat⟩ := collar_bounded_graph_format hQQE s D
  obtain ⟨N,hfib⟩ := collar_uniform_fibers hCell hHardt hQE sOut DOut
  refine ⟨sOut,DOut,N,?_⟩
  intro P m δ c M hP hm hδ hc hc₁ hcL hM C hsmall E hE d v hd hv hV hrates
    retained hretained frame Cframe hframe a b a' b' hab γ γ' A ν r hr hb hγ hseed B hBc hBd hB
  obtain ⟨B',hBc',hBd',hB'⟩ := hformat a' b' (c*m) γ' d v B hBc hBd hB
  let Ω := fluxRectangle a b (c*m)
  let p (x : Coordinates) := γ (x 0)
  let u (x : Coordinates) := fderiv ℝ d (p x) (1,0)
  let V' (x : Coordinates) := fderiv ℝ v (p x) (1,0)+ν (x 0)*fderiv ℝ v (p x) (d (p x),1)
  let L (x : Coordinates) := matrixMap (collarJac (A (x 0)) (ν (x 0)) (d (p x)) (v (p x))
    (u x+ν (x 0)*v (p x)) (V' x) (x 1))
  have hP₀ : 0≤P := by linarith
  have hP₁ : 1≤P := by linarith
  have hdiff (x : Coordinates) (hx : x∈Ω) := by
    have hs := hseed (x 0) hx.1
    exact collar_differential (x:=x) hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
      ((hd _ hs.1).differentiableAt (by norm_num)) (hv _ hs.1) (hV _ hs.1)
  have hdet (x : Coordinates) (hx : x∈Ω) : 1/2≤(L x).det ∧ (L x).det≤3/2 := by
    rw [(hdiff x hx).2]
    have hs := hseed (x 0) hx.1
    have hrate := hrates (p x) hs.1
    have hh : 0≤P^C*δ := mul_nonneg (pow_nonneg hP₀ _) hδ
    have hV' : |V' x|≤2*(P^C*δ) := by
      calc
        |V' x| ≤ |fderiv ℝ v (p x) (1,0)|+|ν (x 0)*fderiv ℝ v (p x) (d (p x),1)| := abs_add ..
        _ ≤ 2*(P^C*δ) := by
          rw [abs_mul]
          have hmul := mul_le_mul hs.2.2.2.2.2 hrate.2.2.1 (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
          linarith only [hrate.2.1,hmul]
    have ht : |x 1|≤m := (abs_le.mpr ⟨hx.2.1.le,hx.2.2.le⟩).trans (by nlinarith)
    exact collar_det_bounds hm hh hsmall hrate.1 hV' ht
  have hfN : ∀ y, Finite {x | x∈Ω ∧ collarMap γ d v x=y} ∧
      Nat.card {x | x∈Ω ∧ collarMap γ d v x=y}≤N :=
    hfib a b a' b' (c*m) γ γ' d v r hr hb hγ B' hBc' hBd' hB'
      (fun x hx => ⟨L x,(hdiff x hx).1,ne_of_gt (lt_of_lt_of_le (by norm_num) (hdet x hx).1)⟩)
  obtain ⟨hQ,_,hl,hu⟩ := flux_rectangle_image_area (collarMap γ d v) a b (c*m) hab L
    (fun x hx => (hdiff x hx).1) hdet N hfN
  obtain ⟨hl',hu'⟩ := collar_area_powers (K:=K) hP (by linarith) hc hc₁ hab hcL hl hu
  refine ⟨?_,hfN,hQ,hl',hu',B',hBc',hBd',hB'⟩
  intro x hx
  have hs := hseed (x 0) hx.1
  have ht : |x 1|≤c*m := abs_le.mpr ⟨hx.2.1.le,hx.2.2.le⟩
  obtain ⟨hxE,hret,hC⟩ := collar_inside_and_slope hP hm hδ hc₁ C hsmall hE hd hv hV
    (fun p hp => (hrates p hp).1) (fun p hp => (hrates p hp).2.2.1)
    (fun p hp => (hrates p hp).2.2.2) retained hretained frame Cframe hframe hs.1 hM hs.2.1 ht
  have hJ := hdet x hx
  obtain ⟨hUV,hVU⟩ := coframe_inverse (ν:=ν (x 0))
    (C:=d (p x)+v (p x)*x 1-d (collarPoint γ d v x))
    (ne_of_gt (lt_of_lt_of_le (by norm_num) hJ.1))
  obtain ⟨hU,hV⟩ := coframe_norms hJ.1 hJ.2 hs.2.2.2.2.2 hC
  have hp : (10:ℝ)≤P^(4+K+N) := calc
    10 ≤ (2:ℝ)^4 := by norm_num
    _ ≤ P^4 := pow_le_pow_left₀ (by norm_num) hP _
    _ ≤ _ := pow_le_pow_right₀ hP₁ (by omega)
  exact ⟨hxE,hret,(hdiff x hx).1,(hdiff x hx).2,coframe_pullback,hUV,hVU,
    hU.trans (by linarith),hV.trans hp⟩

end PaperI.ParabolicCollar
