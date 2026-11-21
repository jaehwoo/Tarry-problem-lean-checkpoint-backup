import Revision.CenteredFlux
import PaperILean.Nov18CollarRouteBudgets
import PaperILean.CommonNullFamily

/-! Source-level parabolic dispatch on the actual short and signed
original cells, preserving their measured chart choice. -/

namespace PaperI.CommonNullAssignment

open Set MeasureTheory MvPolynomial
open scoped ContDiff ENNReal
open PaperI.BoundedCharacteristic PaperI.CorridorBands PaperI.ModerateCorridor
open PaperI.ParabolicCollar PaperI.GoodStrips PaperI.Preparation PaperI.ShortProjectionCaps PaperII.EndpointRangesWhole
open PaperII.QuarticConnection (tangentFrame)

noncomputable section

theorem revised_signed_kernel
    (hDD : PublishedEquispacedDividedDifferenceMeanValue) (hQQE : PublishedQuantitativeRealQE)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) {k : ℕ} (hk : 1≤k) {σ ι : Type} [Finite σ] [DecidableEq ι]
    (F : OriginalNullFamily k σ)
    (N K mPow scalePow ratePow widthPow sizePow coordPow compPow Cf normPow rPow aPow fPow packPow : ℕ)
    (C₀ cutPow : ℝ) (s D : ℕ)
    {RM RA : Set (((NullScalarParameters k σ ⊕ Unit) ⊕ Fin 2) → ℝ)} (hRM : NullDefinable RM) (hRA : NullDefinable RA) :
    ∃ e es sOut DOut bPow : ℕ, ∀ {P m τ M δ T d₁ c CP cR Λ U B : ℝ}
      (_Q : OriginalNullScaleInput P m τ M δ T d₁ c CP cR C₀ cutPow K mPow scalePow ratePow widthPow sizePow coordPow)
      {labels : Finset ι} {rep : (NullScalarParameters k σ → ℝ) → ι → Plane} {fixed : ι → Fin 6 → ℝ}
      (_Z : OriginalNullModelInput F P δ M T Λ U B ratePow compPow Cf normPow rPow aPow fPow packPow labels rep fixed)
      (p : NullScalarParameters k σ → ℝ) {a b : ℝ} {Γ : ℝ → ℝ} {pos : Bool},
      let α := transverseResidual Γ (F.slope p)
      let ell := flux α a b
      let L := roundedDyadicScale (max m ell)
      let W := roundedDyadicScale m
      let read := Sum.elim p (fun _ : Unit => T)
      a<b → 1≤ell → max m ell≤P^sizePow*ell → ContDiffOn ℝ ∞ Γ (Ioo a b) →
      IntervalIntegrable α volume a b → (∀ z∈Ioo a b,residualSign (α z) pos ∧ 1≤|α z|) →
      graphArc a b Γ⊆F.A p →
      (∀ z∈Ioo a b,∀ y,Sum.elim read ![z,y]∈RM ↔ y=Γ z) →
      (∀ z∈Ioo a b,∀ y,Sum.elim read ![z,y]∈RA ↔ y=α z) →
      ∀ (SF : Finset (MvPolynomial (Unit ⊕ Fin 4) ℝ)), SF.card≤s →
        (∀ z∈SF,z.totalDegree≤D) →
        PolynomialSignDetermined SF (originalSeedGraph a b (fun z => (Γ z,z)) (F.slope p) (F.rate p)) →
      ∀ (piece : Finset ι),
      (piece.card : ℝ)≤P^(fPow*packPow+max rPow aPow+ratePow+9)*Λ*(L*W) →
      (∀ i∈piece,(rep p i).2∈Ioo a b ∧ |Γ (rep p i).2-(rep p i).1|≤L ∧
        |F.slope p (Γ (rep p i).2,(rep p i).2)-F.slope p (rep p i)|≤P^(max ratePow compPow)*L ∧
        IntrinsicReach (F.E p) (F.slope p) (rep p i) (Γ (rep p i).2,(rep p i).2) (3*L) ∧
        ∀ j,|fixedEndpointFrame (fixed i) (F.root p) (F.slope p) (rep p i) j|≤P^(max ratePow compPow)) →
      ∃ R : OriginalParabolicBandResult (p ∘ Sum.inl) P Λ δ U B N e es ratePow sOut DOut
        (F.E p) (F.root p) (F.slope p) (F.rate p) (F.retains p) piece (rep p) fixed .transverseCollar (L,W), R.a=0 ∧ R.b=ell ∧ R.w=(P^K)⁻¹*m ∧ (∃ S : TransverseSeed Γ (F.slope p) a b pos, R.γ=S.point) ∧ volume R.patch.region ≤ ENNReal.ofReal (P^bPow)*volume R.certificate.certificate.prepared.goodPhysical ∧
          OriginalParabolicReadoutBudget R (P^bPow) (sizePow+1) K := by
  obtain ⟨e,es,sOut,DOut,C,hFlux⟩ := revised_centered_flux hDD hQQE hCell hHardt hQE hk (ι:=ι)
    N K s D mPow sizePow ratePow Cf (max ratePow compPow) (fPow*packPow+max rPow aPow+ratePow+9)
    (precutFieldReindex_definable hRM) (precutFieldReindex_definable hRA)
    (nullReferenceRelation_definable F.slopeReadout_definable) (nullReferenceRelation_definable F.rate_definable)
    (nullReferenceRelation_definable F.root_definable)
  obtain ⟨bPow,hC⟩ := uniform_constant_le_power C
  refine ⟨e,es,sOut,DOut,bPow,?_⟩
  intro P m τ M δ T d₁ c CP cR Λ U B Q labels rep fixed Z p a b Γ pos α ell L W read
    hab hEll hLen hΓ hI hSign hArc hM hRes SF hSC hSD hS piece hCount hRep
  have hP := Q.P_ge
  have hP₁ : 1≤P := by linarith
  have hτ : 1≤τ := (one_le_pow₀ hP₁).trans Q.cutoff_lower
  have hm : 1≤m := hτ.trans Q.cutoff_le
  have hBuf : 4*m<M := by linarith [Q.buffer]
  have hT : ∃ T',∀ q∈F.E p,|q.1|≤T' ∧ |q.2|≤T' :=
    ⟨T,fun q hq => ⟨by linarith [Z.outer_bounds p q hq,abs_nonneg q.2,abs_nonneg (F.slope p q)],
      by linarith [Z.outer_bounds p q hq,abs_nonneg q.1,abs_nonneg (F.slope p q)]⟩⟩
  have hΓMap : MapsTo (fun z => (Γ z,z)) (Ioo a b) (F.E p) := fun z hz =>
    Z.closure_outer (by linarith) p (subset_closure (hArc ⟨hz,rfl⟩))
  have hα : ContDiffOn ℝ ∞ α (Ioo a b) :=
    (hΓ.deriv_of_isOpen isOpen_Ioo (by simp)).sub
      ((Z.slope_smooth p).comp (hΓ.prodMk contDiff_id.contDiffOn) hΓMap)
  let p' := nullReferenceParameters p T
  have hReadM (z : ℝ) (hz : z∈Ioo a b) (y : ℝ) :
      Sum.elim p' ![z,y]∈precutFieldReindex RM ↔ y=Γ z :=
    (precutFieldReindex_read p T ![z,y] RM).trans (hM z hz y)
  have hReadA (z : ℝ) (hz : z∈Ioo a b) (y : ℝ) :
      Sum.elim p' ![z,y]∈precutFieldReindex RA ↔ y=α z :=
    (precutFieldReindex_read p T ![z,y] RA).trans (hRes z hz y)
  have hLift : L≤P^(max ratePow compPow)*L := le_mul_of_one_le_left
    (zero_le_one.trans (one_le_roundedDyadicScale _)) (one_le_pow₀ hP₁)
  have hRep' (i : ι) (hi : i∈piece) := hRep i hi
  obtain ⟨R,ha,hb,hw,hSeed,hArea,H⟩ := hFlux hP hm Q.m_upper Q.δ_nonneg Q.δ_le Z.packing.nonnegative Z.U_nonnegative Z.B_nonnegative hBuf
    Q.flow_defect Q.cubic_defect (Z.outer_open p) (Z.root_smooth p) (Z.slope_smooth p) (Z.rate_smooth p)
    hab hEll hLen hΓ hI hα hSign (Z.retains p) (Z.boxes p) hArc hT p' hReadM hReadA
    (nullReferenceRelation_realize (F.slope_exact p) T) (nullReferenceRelation_realize (F.rate_exact p) T)
    (nullReferenceRelation_realize (F.root_exact p) T) (Z.original_window p) (Z.curvature_window p)
    SF hSC hSD hS piece (rep p) fixed hCount (fun i hi => ⟨(hRep' i hi).1,(hRep' i hi).2.1.trans hLift,
      (hRep' i hi).2.2.1,((hRep' i hi).2.2.2.1).mono (mul_le_mul_of_nonneg_left hLift (by norm_num)),
      (hRep' i hi).2.2.2.2⟩)

  exact ⟨R,ha,hb,hw,hSeed,hArea.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (hC P hP)) _),{H with constant := ⟨H.constant.1,H.constant.2.trans (hC P hP)⟩}⟩

end

end PaperI.CommonNullAssignment
