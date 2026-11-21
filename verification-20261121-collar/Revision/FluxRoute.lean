import Revision.LongPreparation
import Revision.Physical
import PaperILean.CommonNullParabolicAssembly

/-! Use the original signed flux clock both for all of the original-label
paths and for the full common physical preparation. -/

namespace PaperI.CommonNullAssignment

open Set FirstOrder MeasureTheory MvPolynomial
open scoped ContDiff ENNReal
open PaperI.BoundedCharacteristic PaperI.CorridorBands PaperI.ShortProjectionCaps
open PaperI.GoodStrips PaperI.Preparation PaperI.ParabolicCollar PaperII.EndpointRangesWhole
open PaperII.QuarticConnection (tangentFrame)
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

noncomputable section

private abbrev RD {σ : Type} (G : Set (σ → ℝ)) := (univ : Set ℝ).Definable Language.ring G

theorem revised_phase_flux_route
    (hDD : PublishedEquispacedDividedDifferenceMeanValue) (hQQE : PublishedQuantitativeRealQE)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) {k : ℕ} (hk : 1≤k) {σ ι : Type} [Finite σ] [DecidableEq ι]
    (N K s D sizePow ratePow fixedPow boundPow packPow : ℕ)
    {RM RA : Set ((NullScalarParameters k σ ⊕ Fin 2) → ℝ)}
    {GD GV GC : Set ((NullScalarParameters k σ ⊕ Fin 3) → ℝ)}
    (hRM : RD RM) (hRA : RD RA) (hGD : RD GD) (hGV : RD GV) (hGC : RD GC) :
    ∃ e sOut DOut n : ℕ, ∃ C : ℝ, 1≤C ∧ ∀ {P m δ M Λ U B : ℝ},
      2≤P → 1≤m → 0≤δ → δ≤1 → 0≤Λ → 0≤U → 0≤B → 4*m<M →
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
      ∃ S : TransverseSeed Γ d a b pos,
      ∃ X : NullScale, X.L=L ∧ X.W=W ∧
      ∃ det : Coordinates → ℝ,
        (∀ x∈fluxRectangle 0 ell w,det x=(fderiv ℝ (collarMap S.point d v) x).det) ∧
        (∃ Sg : Finset (MvPolynomial (Fin 2 ⊕ Fin 2) ℝ),
          Sg.card≤sOut ∧ (∀ q∈Sg,q.totalDegree≤DOut) ∧
          PolynomialSignDetermined Sg (originalCollarGraph a b w (fun z => (Γ z,z)) d v)) ∧
        let q₀ := S.point (ell/2)
        ∃ R : ActualPreparedParabolic N e n S.point d v c 0 ell w C P Λ E retained X
          (.transverseCollar S.point 0 ell w)
          (nullScalarRoster F c (nullNormalScalar F c 0 q₀)) (parabolicScalarBudgets k U X.L B)
          (preparedSeedAmplitudes (parabolicScalarBudgets k U X.L B) (P^ratePow) X.L)
          det (d q₀) (q₀.1-d q₀*q₀.2) q₀.2 (Sum.inr 0) (2*U) labels rep fixed,
          volume (collarImage S.point d v 0 ell w) ≤ (6*(n:ℝ≥0∞))*volume R.certificate.prepared.goodPhysical := by
  let J : Empty → Set ((NullScalarParameters k σ ⊕ Fin 3) → ℝ) := Empty.elim
  obtain ⟨e₀,hLong⟩ := prepare_collar_with_polynomial_bridge hDD hQQE hCell hHardt hQE (ι:=ι)
    N K s D sizePow ratePow fixedPow boundPow packPow J (curveAsField RA) (fun i => i.elim)
    (curveAsField_definable hRA)
  obtain ⟨sOut,DOut,n,hGeom⟩ := transverse_collar_of_signed_graph hQQE hCell hHardt hQE s D K
  obtain ⟨C,hC,hPrep⟩ := prepare_original_parent_on_actual_flux hDD hCell hHardt hQE hk N hRM hRA hGD hGV hGC
  obtain ⟨e,hAssembly⟩ := assemble_actual_prepared_parabolic (ι:=ι) (κ₀:=Empty)
    (κ:=NullReadoutIndex k) C n e₀ (sizePow+K+2)
  refine ⟨max e e₀,sOut,DOut,n,C,hC,?_⟩
  intro P m δ M Λ U B hP hm hδ hδ₁ hΛ hU hB hM hFlow hSmall
    a b Γ d v c pos A E retained frame w α ell L W
    hE hc hd hv hab hEll hLenPow hΓ hI hα hSign hRetain box hArc hBound
    p F hRM' hRA' hD hV hG hNorm hCurv SF hCard hDeg hFormat labels rep fixed hCount hRep
  obtain ⟨old⟩ := hLong hP hm hδ hδ₁ hΛ hM hFlow hSmall hab hEll hLenPow hΓ hI hα hSign hRetain box hArc p
    (Empty.elim : Empty → Plane → ℝ) (Empty.elim : Empty → ℝ) (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim) (curveAsField_readout hRA') (fun i => i.elim)
    SF hCard hDeg hFormat labels rep fixed hCount hRep
  let S := old.seed
  let X := old.scale
  have hX := old.long_eq
  have hXW := old.wide_eq
  have hP₁ : 1≤P := by linarith
  have hwpos : 0<(P^K)⁻¹ := by positivity
  have hwP : (P^K)⁻¹≤1 := inv_le_one_of_one_le₀ (one_le_pow₀ hP₁)
  have hw : 0<w := by dsimp [w]; positivity
  have hw₀ : w≤m := mul_le_of_le_one_left (by linarith) hwP
  have hLen : ell≤X.L := by rw [hX]; exact (le_max_right _ _).trans (le_roundedDyadicScale _)
  have hWL : w≤X.L := by rw [hX]; exact hw₀.trans ((le_max_left _ _).trans (le_roundedDyadicScale _))
  obtain ⟨Q⟩ := hGeom hP hm hδ hwpos hwP le_rfl hM ratePow fixedPow hSmall hRetain box hArc S
    (by linarith : 0≤ell) SF hCard hDeg hFormat
  have hBox (r : ℝ) (hr : r∈Ioo 0 ell) : CertifiedBox P δ M ratePow fixedPow E d v frame (S.point r) := by
    have hT : r∈S.clock.val.target := by rw [S.clock.property.2.1]; exact hr
    have hS := S.clock.val.map_target hT
    rw [S.clock.property.1] at hS
    exact box _ (hArc ⟨(congrArg Prod.snd (S.original_height r hr)).symm ▸ hS,
      congrArg Prod.fst (S.original_height r hr) |>.trans
        (congrArg Γ (congrArg Prod.snd (S.original_height r hr))).symm⟩)
  obtain ⟨V⟩ := hPrep S Q hP hm hδ hδ₁ hM hFlow hSmall (by linarith : 0<ell) hw hw₀ hWL X.L_one hLen hU
    hI hα (fun z hz => (hSign z hz).1) hΓ hBox hE hc hd hv p hRM' hRA' hD hV hG hNorm hCurv
  have hSX : X.S≤P^(sizePow+K+2)*((ell-(0:ℝ))*w) := by
    have hLL : X.L≤2*max m ell := hX.symm ▸
      (by simpa only [max_eq_right (hm.trans (le_max_left _ _))] using
        (roundedDyadicScale_lt_two_max (max m ell)).le)
    have hLL' : X.L≤2*(P^sizePow*ell) := hLL.trans (mul_le_mul_of_nonneg_left hLenPow (by norm_num))
    have hWW : X.W≤2*m := hXW.symm ▸
      (by simpa only [max_eq_right hm] using (roundedDyadicScale_lt_two_max m).le)
    have hM_w : m=P^K*w := by
      dsimp only [w]
      rw [← mul_assoc,mul_inv_cancel₀ (by positivity),one_mul]
    have h₂ : (4:ℝ)≤P^2 := by nlinarith
    have h₀ : 0≤P^(sizePow+K) := by positivity
    calc
      _ ≤ (2*(P^sizePow*ell))*(2*m) := mul_le_mul hLL' hWW (by linarith [X.W_one]) (by positivity)
      _ = (P^(sizePow+K)*4)*((ell-0)*w) := by rw [hM_w,pow_add]; ring
      _ ≤ _ := by
        rw [pow_add P (sizePow+K) 2]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₂ h₀)
          (mul_nonneg (by linarith) hw.le)
  obtain ⟨out⟩ := hAssembly hP hΛ (by linarith : 0<ell) hw
    (parabolicScalarBudgets_nonnegative hU (by linarith [X.L_one]) hB)
    (fun _ => rfl) (bounded_physical_carrier_volume hBound) hSX V old.certificate
    (Or.inl old.patch_eq) old.fixed_ranges
  refine ⟨S,X,hX,hXW,(fun x => (Q.differential x).det),?_,Q.original_format,?_⟩
  · intro x hx
    rw [(Q.derivative x hx).fderiv]
  · let R := old.patch_eq ▸ out
    refine ⟨R,?_⟩
    rw [R.certificate.prepared.goodPhysical_eq,R.same_good,R.patch_eq]
    exact PaperI.CollarRevision.comparable_good Q (by linarith) R.germ.base.physical_area

end

end PaperI.CommonNullAssignment
