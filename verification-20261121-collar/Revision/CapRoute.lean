import Revision.Physical
import Revision.FreshPreparation

/-! Joint preparation on the exact horizontal seed in the revised Lemma 3.16. -/

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

theorem exact_phase_literal_cap_route
    (hDD : PublishedEquispacedDividedDifferenceMeanValue) (hQQE : PublishedQuantitativeRealQE)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) {k : ℕ} (hk : 1≤k) {σ ι : Type} [Finite σ] [DecidableEq ι]
    (N K s D ratePow compPow framePow normPow packPow sCap DCap nCap : ℕ)
    {GD GV GC : Set ((NullScalarParameters k σ ⊕ Fin 3) → ℝ)}
    (hGD : RD GD) (hGV : RD GV) (hGC : RD GC) :
    ∃ e sOut DOut n : ℕ, ∃ C : ℝ, 1≤C ∧ ∀ {P m τ δ M Λ U B : ℝ},
      2≤P → 1≤m → 0<τ → τ≤m → 0≤δ → δ≤1 → 0≤Λ → 0≤U → 0≤B →
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
      let q₀ := γ ((a+b)/2)
      ∃ X : NullScale, X.L=capLength I m ∧ X.W=roundedDyadicScale m ∧
      ∃ det : Coordinates → ℝ,
        (∀ x∈fluxRectangle a b w,det x=(fderiv ℝ (collarMap γ d v) x).det) ∧
        (∃ Sg : Finset (MvPolynomial (Fin 2 ⊕ Fin 2) ℝ),
          Sg.card≤sOut ∧ (∀ q∈Sg,q.totalDegree≤DOut) ∧
          PolynomialSignDetermined Sg (originalCollarGraph a b w γ d v)) ∧
        ∃ R : ActualPreparedParabolic N e n γ d v c a b w C P Λ E keep X (.cap a b z w)
          (nullScalarRoster F c (nullNormalScalar F c 0 q₀)) (parabolicScalarBudgets k U X.L B)
          (preparedSeedAmplitudes (parabolicScalarBudgets k U X.L B) (P^ratePow) X.L)
          det (d q₀) (q₀.1-d q₀*q₀.2) q₀.2 (Sum.inr 0) (2*U) labels rep fixed,
          volume (collarImage γ d v a b w) ≤ (6*(n:ℝ≥0∞))*volume R.certificate.prepared.goodPhysical := by
  let J : Empty → Set ((Unit ⊕ Fin 3) → ℝ) := Empty.elim
  obtain ⟨e₀,hCap⟩ := prepare_original_cap_certificate hDD hQQE hCell hHardt hQE (ι:=ι)
    N K s D ratePow compPow framePow normPow packPow sCap DCap nCap J (fun i => i.elim)
  obtain ⟨sOut,DOut,n,hGeom⟩ := horizontal_cap_differential hQQE hCell hHardt hQE s D K
  obtain ⟨C,hC,hPrep⟩ := prepare_original_parent_on_actual_cap hDD hCell hHardt hQE hk N hGD hGV hGC
  obtain ⟨e,hAssembly⟩ := assemble_inner_cap (ι:=ι) (κ₀:=Empty)
    (κ:=NullReadoutIndex k) C n e₀ (K+3)
  refine ⟨e,sOut,DOut,n,C,hC,?_⟩
  intro P m τ δ M Λ U B hP hm hτ hτm hδ hδ₁ hΛ hU hB hM hFlow hSmall
    A E Ω d v c keep Frame hE hc hd hv hKeep hBound box hSub hConn labels rep fixed flow hRep hComp Cap
    SF hCard hDeg hFormat p F hD hV hG hNorm hCurv I a b z w γ q₀
  have hReg (q : Plane) (hq : q∈E) : ContDiffAt ℝ 1 d q :=
    (hd.contDiffAt (hE.mem_nhds hq)).of_le (by simp)
  obtain ⟨old⟩ := hCap hP hm hτ hτm hδ hδ₁ hΛ hM hFlow hSmall hKeep hReg hBound box hSub hConn
    labels rep fixed flow hRep hComp Cap SF hCard hDeg hFormat (fun _ => 0)
    (Empty.elim : Empty → Plane → ℝ) (Empty.elim : Empty → ℝ)
    (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
  let X := old.scale
  have hX := old.long_eq
  have hXW := old.wide_eq
  have hEq : b-a = max m (horizontalSpan I) := cap_length I m
  have hRaw : m≤b-a := hEq.symm ▸ le_max_left ..
  have hab : a<b := by linarith
  have hw : 0<w := by dsimp [w]; positivity
  have hw₀ : w≤m := by
    dsimp only [w]
    exact mul_le_of_le_one_left (by linarith)
      (inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith)))
  have hLen : b-a≤X.L := by rw [hEq,hX]; exact Cap.scales.2.2.1
  obtain ⟨hLo,hHi⟩ := projection_bounded Cap hτ hBound
  have hIncl := (cap_geometry (hConn.nonempty.image (project Ω flow)) hLo hHi (by linarith : 0≤m)).2.1
  have hInner : Ioo a b ⊆ Ioo (leftEnd I m) (rightEnd I m) := by
    intro x hx
    exact ⟨lt_of_le_of_lt (hIncl (show a∈Icc a b from ⟨le_rfl,hab.le⟩)).1 hx.1,
      lt_of_lt_of_le hx.2 (hIncl (show b∈Icc a b from ⟨hab.le,le_rfl⟩)).2⟩
  have hWL : w≤X.L := hw₀.trans (hRaw.trans hLen)
  have hML : 4*m<M-τ-m := by linarith
  have hBox (q : ℝ) (hq : q∈Ioo a b) : CertifiedBox P δ (M-τ-m) ratePow framePow E d v Frame (γ q) :=
    Classical.choice (cap_horizontal_seed_boxes hP hm hτ hτm hM hδ hFlow hReg hSub hConn hBound box Cap
      q (hIncl (Ioo_subset_Icc_self hq)))
  obtain ⟨Q⟩ := hGeom hP hm hδ hML ratePow framePow hSmall E d v Frame keep hKeep hab.le hBox
    SF hCard hDeg hFormat
  obtain ⟨V⟩ := hPrep Q hP hm hδ hδ₁ hML hFlow hSmall hab hw hw₀ hWL X.L_one hLen hU hBox hE hc hd hv p
    hD hV hG hNorm hCurv
  have hSX : X.S≤P^(K+3)*((b-a)*w) := by
    have hLL : X.L≤4*(b-a) := by rw [hX,hEq]; exact Cap.scales.2.2.2.1
    have hWW : X.W≤2*m := hXW.symm ▸
      (by simpa only [max_eq_right hm] using (roundedDyadicScale_lt_two_max m).le)
    have hM_w : m=P^K*w := by
      dsimp only [w]
      rw [← mul_assoc,mul_inv_cancel₀ (by positivity),one_mul]
    calc
      _ ≤ (4*(b-a))*(2*m) := mul_le_mul hLL hWW (zero_le_one.trans X.W_one)
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hab.le))
      _ = 8*P^K*((b-a)*w) := by rw [hM_w]; ring
      _ ≤ _ := by
        rw [pow_add]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (sub_nonneg.mpr hab.le) hw.le)
        rw [mul_comm 8]
        exact mul_le_mul_of_nonneg_left ((by norm_num : (8:ℝ)≤2^3).trans (pow_le_pow_left₀ (by norm_num) hP 3)) (by positivity)
  have hRegion : (NullPatch.cap a b z w : NullPatch d v).region ⊆ old.certificate.prepared.patch.region := by
    rw [old.patch_eq]
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨u,⟨hInner hu.1,hu.2⟩,rfl⟩
  obtain ⟨out⟩ := hAssembly hP hΛ hab hw (parabolicScalarBudgets_nonnegative hU (by linarith [X.L_one]) hB)
    (fun _ => rfl) (bounded_physical_carrier_volume hBound) hSX
    (by linarith [X.L_one] : X.L≤4*X.L) (by linarith [X.S_one] : X.S≤4*X.S)
    V old.certificate hRegion old.fixed_ranges
  refine ⟨X,hX,hXW,(fun x => (Q.differential x).det),?_,Q.original_format,?_⟩
  · intro x hx
    rw [(Q.derivative x hx).fderiv]
  · refine ⟨out,?_⟩
    rw [out.certificate.prepared.goodPhysical_eq,out.same_good,out.patch_eq]
    exact comparable_good Q hab.le out.germ.base.physical_area

end

end PaperI.CommonNullAssignment
