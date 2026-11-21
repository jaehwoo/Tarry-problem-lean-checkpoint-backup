import Revision.CapRoute
import PaperILean.Nov18CollarRouteBudgets

namespace PaperI.CommonNullAssignment

open Set FirstOrder MeasureTheory MvPolynomial
open scoped ContDiff ENNReal
open PaperI.BoundedCharacteristic PaperI.CorridorBands PaperI.ShortProjectionCaps
open PaperI.GoodStrips PaperI.Preparation PaperI.ParabolicCollar PaperII.EndpointRangesWhole
open PaperII.QuarticConnection (tangentFrame)
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

open PaperI.CollarRevision

noncomputable section

private abbrev RD {σ : Type} (G : Set (σ → ℝ)) := (univ : Set ℝ).Definable Language.ring G

theorem exact_phase_centered_cap_with_budget
    (hDD : PublishedEquispacedDividedDifferenceMeanValue) (hQQE : PublishedQuantitativeRealQE)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) {k : ℕ} (hk : 1≤k) {σ ι : Type} [Finite σ] [DecidableEq ι]
    (N K s D mPow ratePow compPow framePow normPow packPow sCap DCap nCap : ℕ)
    {GD GV GC : Set ((NullScalarParameters k σ ⊕ Fin 3) → ℝ)}
    (hGD : RD GD) (hGV : RD GV) (hGC : RD GC) :
    ∃ e es sOut DOut : ℕ, ∃ Cbound : ℝ, ∀ {P m τ δ M Λ U B : ℝ},
      2≤P → 1≤m → m≤P^mPow → 0<τ → τ≤m → 0≤δ → δ≤1 → 0≤Λ → 0≤U → 0≤B →
      τ+6*m+1<M → P^ratePow*δ*(2*m)≤Real.log 2 → P^ratePow*δ*m^3≤1/16 →
      ∀ {A E Ω : Set Plane} {d v c : Plane → ℝ} {keep : Plane → Prop} {Frame : Plane → Fin 6 → ℝ},
      IsOpen E → ContDiffOn ℝ ∞ c E → ContDiffOn ℝ ∞ d E → ContDiffOn ℝ ∞ v E →
      (∀ p∈E,keep p) → (∃ R, ∀ p∈E,|p.1|≤R ∧ |p.2|≤R) →
      (∀ p∈A,CertifiedBox P δ M ratePow framePow E d v Frame p) →
      Ω⊆A → IsConnected Ω →
      ∀ (labels : Finset ι) (rep : ι → Plane) (fixed : ι → Fin 6 → ℝ) (flow : Plane → ℝ → ℝ),
      (∀ i∈labels,rep i∈Ω) →
      (∀ i∈labels,∀ j,|fixedEndpointFrame (fixed i) c d (rep i) j|≤P^compPow) →
      PhaseCap P m τ Λ K packPow framePow normPow sCap DCap nCap E Ω d v keep flow labels rep →
      ∀ Afield : Finset (MvPolynomial (Fin 4) ℝ), Afield.card≤s →
        (∀ p∈Afield,p.totalDegree≤D) → PolynomialSignDetermined Afield (ShortProjectionCaps.fieldGraph E d v) →
      ∀ p : NullScalarParameters k σ → ℝ,
      let F := p ∘ Sum.inl
      RealizesOn GD p d E → RealizesOn GV p v E → RealizesOn GC p c E →
      (∀ q∈E,coefficientEuclideanNorm (originalUpperCoefficientPullback F (tangentFrame c d q))≤U) →
      (∀ q∈E,|derivX (derivX c) q|≤B) →
      let I := project Ω flow '' Ω
      let a := capLeft I m
      let b := capRight I m
      let z := midheight Ω
      let w := (P^K)⁻¹*m
      let γ := horizontalSeed z
      ∃ Q : OriginalParabolicBandResult F P Λ δ U B N e es ratePow sOut DOut E c d v keep labels rep fixed
        .cap (capLength I m,capWidth m), Q.a=a ∧ Q.b=b ∧ Q.γ=γ ∧ Q.w=w ∧ Q.b-Q.a=max m (horizontalSpan I) ∧
          volume Q.patch.region ≤ ENNReal.ofReal Cbound * volume Q.certificate.certificate.prepared.goodPhysical ∧
        OriginalParabolicReadoutBudget Q Cbound 2 K := by
  obtain ⟨e,sOut,DOut,n,C,hC,hCap⟩ := exact_phase_literal_cap_route hDD hQQE hCell hHardt hQE hk
    (ι:=ι) N K s D ratePow compPow framePow normPow packPow sCap DCap nCap hGD hGV hGC
  obtain ⟨es,hCenter⟩ := actual_parabolic_certificate_centered C ratePow mPow 2 K N
  refine ⟨e,es,sOut,DOut,max C (6*(n:ℝ)),?_⟩
  intro P m τ δ M Λ U B hP hm hmPow hτ hτm hδ hδ₁ hΛ hU hB hM hFlow hSmall
    A E Ω d v c keep Frame hE hc hd hv hKeep hBound box hSub hConn labels rep fixed flow hRep hComp Cap
    SF hCard hDeg hFormat p F hD hV hG hNorm hCurv I a b z w γ
  obtain ⟨X,hXL,hXW,det,hDet,hFmt,R,hArea⟩ := hCap hP hm hτ hτm hδ hδ₁ hΛ hU hB hM hFlow hSmall
    hE hc hd hv hKeep hBound box hSub hConn labels rep fixed flow hRep hComp Cap SF hCard hDeg hFormat
    p hD hV hG hNorm hCurv
  have hP₁ : 1≤P := by linarith
  have hEq : b-a=max m (horizontalSpan I) := cap_length I m
  have hRaw : m≤b-a := hEq.symm ▸ le_max_left ..
  have hab : a<b := by linarith
  have hw : 0<w := by dsimp [w]; positivity
  have hwm : w≤m :=
    mul_le_of_le_one_left (by linarith) (inv_le_one_of_one_le₀ (one_le_pow₀ hP₁))
  have hLen : b-a≤X.L := by rw [hXL,hEq]; exact Cap.scales.2.2.1
  have hwL : w≤X.L := hwm.trans (hRaw.trans hLen)
  have hL' : X.L≤P^2*(b-a) := by
    rw [hXL,hEq]
    exact Cap.scales.2.2.2.1.trans (mul_le_mul_of_nonneg_right (by nlinarith) (le_max_of_le_left (by linarith)))
  obtain ⟨hLo,hHi⟩ := projection_bounded Cap hτ hBound
  have hIncl := (cap_geometry (hConn.nonempty.image (project Ω flow)) hLo hHi (by linarith : 0≤m)).2.1
  have hw' : (P^K)⁻¹≤2*w := by
    change (P^K)⁻¹≤2*((P^K)⁻¹*m)
    have h : (P^K)⁻¹≤(P^K)⁻¹*m := le_mul_of_one_le_right (by positivity) hm
    exact h.trans (le_mul_of_one_le_left (by positivity) (by norm_num))
  have hML : 4*m<M-τ-m := by linarith
  have hReg (q : Plane) (hq : q∈E) : ContDiffAt ℝ 1 d q :=
    (hd.contDiffAt (hE.mem_nhds hq)).of_le (by simp)
  have hB (q : ℝ) (hq : q∈Ioo a b) : CertifiedBox P δ (M-τ-m) ratePow framePow E d v Frame (γ q) :=
    Classical.choice (cap_horizontal_seed_boxes hP hm hτ hτm hM hδ hFlow hReg hSub hConn hBound box Cap
      q (hIncl (Ioo_subset_Icc_self hq)))
  have hSeed' (s : ℝ) (_ : s∈Ioo a b) : HasDerivAt (fun u => (γ u).1) 1 s ∧
      HasDerivAt (fun u => (γ u).2) 0 s ∧ (1:ℝ)-d (γ s)*0=1 ∧ |(0:ℝ)|≤1 :=
    ⟨hasDerivAt_id _,hasDerivAt_const _ _,by ring,by norm_num⟩
  have hγ : ContDiffOn ℝ ∞ γ (Ioo a b) := contDiff_id.contDiffOn.prodMk contDiffOn_const
  have hMap : MapsTo γ (Ioo a b) E := fun s hs => (hB s hs).carrier_subset (hB s hs).mem_carrier
  refine ⟨⟨X,a,b,w,γ,C,n,det,.cap a b z w,Or.inl ⟨z,rfl,rfl,rfl⟩,?_,hDet,?_,(a+b)/2,rfl,
    R,?_,Prod.ext hXL hXW⟩,rfl,rfl,rfl,rfl,hEq,?_,?_⟩
  · intro s hs
    obtain ⟨h₁,h₂,h₃,h₄⟩ := hSeed' s hs
    rw [h₁.deriv,h₂.deriv]
    exact ⟨h₃,h₄⟩
  · obtain ⟨Sg,hs,hD,hFmt'⟩ := hFmt
    exact ⟨a,b,γ,Sg,hs,hD,hFmt',original_collar_format_projection a b w γ d v⟩
  · exact hCenter hC hP hm hmPow hδ hδ₁ hML hFlow hSmall hw hwm hwL hLen (sub_pos.mpr hab) hL' hw'
      (by constructor <;> linarith : (a+b)/2∈Ioo a b) hB hSeed' hγ (hd.comp hγ hMap) (hv.comp hγ hMap) R
  · apply hArea.trans
    apply mul_le_mul_right'
    have h6 : (6*(n:ℝ≥0∞)) = ENNReal.ofReal (6*(n:ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤6)]
      norm_num
    rw [h6]
    exact ENNReal.ofReal_le_ofReal (le_max_right ..)
  · exact ⟨⟨hC,le_max_left ..⟩,sub_pos.mpr hab,by change 0 < 2*w; positivity,hL',hw',hγ,hd.comp hγ hMap,hv.comp hγ hMap⟩

end

end PaperI.CommonNullAssignment
