import Revision.FluxRoute
import PaperILean.Nov18CollarRouteBudgets

namespace PaperI.CommonNullAssignment

open Set FirstOrder MeasureTheory MvPolynomial
open scoped ContDiff ENNReal
open PaperI.BoundedCharacteristic PaperI.CorridorBands PaperI.ShortProjectionCaps
open PaperI.GoodStrips PaperI.Preparation PaperI.ParabolicCollar PaperII.EndpointRangesWhole
open PaperII.QuarticConnection (tangentFrame)
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

noncomputable section

private abbrev RD {σ : Type} (G : Set (σ → ℝ)) := (univ : Set ℝ).Definable Language.ring G

theorem revised_centered_flux
    (hDD : PublishedEquispacedDividedDifferenceMeanValue) (hQQE : PublishedQuantitativeRealQE)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) {k : ℕ} (hk : 1≤k) {σ ι : Type} [Finite σ] [DecidableEq ι]
    (N K s D mPow sizePow ratePow fixedPow boundPow packPow : ℕ)
    {RM RA : Set ((NullScalarParameters k σ ⊕ Fin 2) → ℝ)}
    {GD GV GC : Set ((NullScalarParameters k σ ⊕ Fin 3) → ℝ)}
    (hRM : RD RM) (hRA : RD RA) (hGD : RD GD) (hGV : RD GV) (hGC : RD GC) :
    ∃ e es sOut DOut : ℕ, ∃ Cbound : ℝ, ∀ {P m δ M Λ U B : ℝ},
      2≤P → 1≤m → m≤P^mPow → 0≤δ → δ≤1 → 0≤Λ → 0≤U → 0≤B → 4*m<M →
      (P^ratePow*δ)*(2*m)≤Real.log 2 → (P^ratePow*δ)*m^3≤1/16 →
      ∀ {a b : ℝ} {Γ : ℝ → ℝ} {d v c : Plane → ℝ} {pos : Bool} {A E : Set Plane}
      {retained : Plane → Prop} {frame : Plane → Fin 6 → ℝ},
      let w := (P^K)⁻¹*m
      let α := transverseResidual Γ d
      let ell := flux α a b
      let L := roundedDyadicScale (max m ell)
      let W := roundedDyadicScale m
      IsOpen E → ContDiffOn ℝ ∞ c E → ContDiffOn ℝ ∞ d E → ContDiffOn ℝ ∞ v E →
      a<b → 1≤ell → max m ell≤P^sizePow*ell → ContDiffOn ℝ ∞ Γ (Ioo a b) →
      IntervalIntegrable α volume a b → ContDiffOn ℝ ∞ α (Ioo a b) →
      (∀ z∈Ioo a b,residualSign (α z) pos ∧ 1≤|α z|) →
      (∀ q∈E,retained q) → (∀ q∈A,CertifiedBox P δ M ratePow fixedPow E d v frame q) →
      graphArc a b Γ ⊆ A → (∃ R, ∀ p∈E,|p.1|≤R ∧ |p.2|≤R) →
      ∀ (p : NullScalarParameters k σ → ℝ),
      let F := p ∘ Sum.inl
      (∀ z∈Ioo a b,∀ y,Sum.elim p ![z,y]∈RM ↔ y=Γ z) →
      (∀ z∈Ioo a b,∀ y,Sum.elim p ![z,y]∈RA ↔ y=α z) →
      RealizesOn GD p d E → RealizesOn GV p v E → RealizesOn GC p c E →
      (∀ q∈E,coefficientEuclideanNorm (originalUpperCoefficientPullback F (tangentFrame c d q))≤U) →
      (∀ q∈E,|derivX (derivX c) q|≤B) →
      ∀ (seedFormat : Finset (MvPolynomial (Unit ⊕ Fin 4) ℝ)),seedFormat.card≤s →
      (∀ q∈seedFormat,q.totalDegree≤D) →
      PolynomialSignDetermined seedFormat (originalSeedGraph a b (fun z => (Γ z,z)) d v) →
      ∀ (labels : Finset ι) (rep : ι → Plane) (fixed : ι → Fin 6 → ℝ),
      (labels.card : ℝ)≤P^packPow*Λ*(L*W) →
      (∀ i∈labels,(rep i).2∈Ioo a b ∧ |Γ (rep i).2-(rep i).1|≤P^boundPow*L ∧
        |d (Γ (rep i).2,(rep i).2)-d (rep i)|≤P^boundPow*L ∧
        IntrinsicReach E d (rep i) (Γ (rep i).2,(rep i).2) (3*(P^boundPow*L)) ∧
        ∀ j,|fixedEndpointFrame (fixed i) c d (rep i) j|≤P^boundPow) →
      ∃ Q : OriginalParabolicBandResult F P Λ δ U B N e es ratePow sOut DOut E c d v retained labels rep fixed
        .transverseCollar (L,W), Q.a=0 ∧ Q.b=ell ∧ Q.w=w ∧ (∃ S : TransverseSeed Γ d a b pos, Q.γ=S.point) ∧ volume Q.patch.region ≤ ENNReal.ofReal Cbound * volume Q.certificate.certificate.prepared.goodPhysical ∧
        OriginalParabolicReadoutBudget Q Cbound (sizePow+1) K := by
  obtain ⟨e,sOut,DOut,n,C,hC,hFlux⟩ := revised_phase_flux_route hDD hQQE hCell hHardt hQE hk
    (ι:=ι) N K s D sizePow ratePow fixedPow boundPow packPow hRM hRA hGD hGV hGC
  obtain ⟨es,hCenter⟩ := actual_parabolic_certificate_centered C ratePow mPow (sizePow+1) K N
  refine ⟨e,es,sOut,DOut,max C (6*(n:ℝ)),?_⟩
  intro P m δ M Λ U B hP hm hmPow hδ hδ₁ hΛ hU hB hM hFlow hSmall
    a b Γ d v c pos A E retained frame w α ell L W
    hE hc hd hv hab hEll hLenPow hΓ hI hα hSign hRetain box hArc hBound
    p F hRM' hRA' hD hV hG hNorm hCurv SF hCard hDeg hFormat labels rep fixed hCount hRep
  obtain ⟨S,X,hXL,hXW,det,hDet,hFmt,R,hArea⟩ := hFlux hP hm hδ hδ₁ hΛ hU hB hM hFlow hSmall
    hE hc hd hv hab hEll hLenPow hΓ hI hα hSign hRetain box hArc hBound p
    hRM' hRA' hD hV hG hNorm hCurv SF hCard hDeg hFormat labels rep fixed hCount hRep
  have hP₁ : 1≤P := by linarith
  have hell : 0<ell := by linarith
  have hw : 0<w := by dsimp [w]; positivity
  have hwm : w≤m :=
    mul_le_of_le_one_left (by linarith) (inv_le_one_of_one_le₀ (one_le_pow₀ hP₁))
  have hLen : ell≤X.L := by rw [hXL]; exact (le_max_right _ _).trans (le_roundedDyadicScale _)
  have hwL : w≤X.L := by rw [hXL]; exact hwm.trans ((le_max_left _ _).trans (le_roundedDyadicScale _))
  have hL' : X.L≤P^(sizePow+1)*ell := by
    rw [hXL,pow_succ]
    have h := (roundedDyadicScale_lt_two_max (max m ell)).le
    rw [max_eq_right (hm.trans (le_max_left _ _))] at h
    calc
      _ ≤ 2*max m ell := h
      _ ≤ 2*(P^sizePow*ell) := mul_le_mul_of_nonneg_left hLenPow (by norm_num)
      _ = (P^sizePow*ell)*2 := by ring
      _ ≤ (P^sizePow*ell)*P := mul_le_mul_of_nonneg_left hP (mul_nonneg (by positivity) hell.le)
      _ = _ := by ring
  have hw' : (P^K)⁻¹≤2*w := by
    change (P^K)⁻¹≤2*((P^K)⁻¹*m)
    have h : (P^K)⁻¹≤(P^K)⁻¹*m := le_mul_of_one_le_right (by positivity) hm
    exact h.trans (le_mul_of_one_le_left (by positivity) (by norm_num))
  have hBox (r : ℝ) (hr : r∈Ioo 0 ell) : CertifiedBox P δ M ratePow fixedPow E d v frame (S.point r) := by
    have hT : r∈S.clock.val.target := by rw [S.clock.property.2.1]; exact hr
    have hS := S.clock.val.map_target hT
    rw [S.clock.property.1] at hS
    apply box _ (hArc ?_)
    rw [S.original_height r hr]
    exact ⟨hS,rfl⟩
  have hMap : MapsTo S.point (Ioo 0 ell) E := fun s hs => (hBox s hs).carrier_subset (hBox s hs).mem_carrier
  have hγ := original_signed_seed_contDiffOn S hΓ hα (fun z hz => (hSign z hz).1)
  have hCenter' := hCenter (γ:=S.point) (a:=(0:ℝ)) (b:=ell) (X:=X) (s₀:=ell/2) (B:=parabolicScalarBudgets k U X.L B)
    hC hP hm hmPow hδ hδ₁ hM hFlow hSmall hw hwm hwL
    (by simpa only [sub_zero] using hLen) (by simpa only [sub_zero] using hell)
    (by simpa only [sub_zero] using hL') hw' (by constructor <;> linarith : ell/2∈Ioo 0 ell)
    hBox S.derivative hγ (hd.comp hγ hMap) (hv.comp hγ hMap) R
  refine ⟨⟨X,0,ell,w,S.point,C,n,det,.transverseCollar S.point 0 ell w,Or.inr ⟨rfl,rfl⟩,
    ?_,hDet,?_,ell/2,by rw [zero_add],R,hCenter',Prod.ext hXL hXW⟩,rfl,rfl,rfl,⟨S,rfl⟩,?_,?_⟩
  · intro s hs
    obtain ⟨h₁,h₂,h₃,h₄⟩ := S.derivative s hs
    rw [h₁.deriv,h₂.deriv]
    exact ⟨h₃,h₄⟩
  · obtain ⟨Sg,hs,hD,hFmt'⟩ := hFmt
    exact ⟨a,b,fun z => (Γ z,z),Sg,hs,hD,hFmt',signed_collar_format_projection S⟩

  · apply hArea.trans
    apply mul_le_mul_right'
    have h6 : (6*(n:ℝ≥0∞)) = ENNReal.ofReal (6*(n:ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤6)]
      norm_num
    rw [h6]
    exact ENNReal.ofReal_le_ofReal (le_max_right ..)
  · exact ⟨⟨hC,le_max_left ..⟩,by simpa only [sub_zero] using hell,by change 0 < 2*w; positivity,
      by simpa only [sub_zero] using hL',hw',hγ,hd.comp hγ hMap,hv.comp hγ hMap⟩

end

end PaperI.CommonNullAssignment
