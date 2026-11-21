import Revision.CenteredCap
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

theorem exact_cap_kernel
    (hDD : PublishedEquispacedDividedDifferenceMeanValue) (hQQE : PublishedQuantitativeRealQE)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) {k : ℕ} (hk : 1≤k) {σ ι : Type} [Finite σ] [DecidableEq ι]
    (F : OriginalNullFamily k σ)
    (N K mPow scalePow ratePow widthPow sizePow coordPow compPow Cf normPow rPow aPow fPow packPow : ℕ)
    (C₀ cutPow : ℝ) (s D sCap DCap nCap : ℕ)
    (BF : Finset (MvPolynomial (NullScalarParameters k σ ⊕ Fin 4) ℝ)) (hBF : BF.card≤s)
    (hBD : ∀ q∈BF,q.totalDegree≤D)
    (hBgraph : PolynomialSignDetermined BF
      (ShortProjectionCaps.jointFieldGraph (capOrderedCell F.outer) F.slope F.rate)) :
    ∃ e es sOut DOut bPow : ℕ, ∀ {P m τ M δ T d₁ c CP cR Λ U B : ℝ}
      (_Q : OriginalNullScaleInput P m τ M δ T d₁ c CP cR C₀ cutPow K mPow scalePow ratePow widthPow sizePow coordPow)
      {labels : Finset ι} {rep : (NullScalarParameters k σ → ℝ) → ι → Plane} {fixed : ι → Fin 6 → ℝ}
      (Z : OriginalNullModelInput F P δ M T Λ U B ratePow compPow Cf normPow rPow aPow fPow packPow labels rep fixed)
      (p : NullScalarParameters k σ → ℝ) {Ω : Set Plane}, Ω⊆F.A p → IsConnected Ω →
      ∀ (piece : Finset ι), piece⊆Z.active p → (∀ i∈piece,rep p i∈Ω) →
      ∀ (flow : Plane → ℝ → ℝ),
      PhaseCap P m τ Λ K packPow Cf normPow sCap DCap nCap (F.E p) Ω
        (F.slope p) (F.rate p) (F.retains p) flow piece (rep p) →
      ∃ R : OriginalParabolicBandResult (p ∘ Sum.inl) P Λ δ U B N e es ratePow sOut DOut
        (F.E p) (F.root p) (F.slope p) (F.rate p) (F.retains p) piece (rep p) fixed .cap
        (capLength (project Ω flow '' Ω) m,capWidth m), R.a=CollarRevision.capLeft (project Ω flow '' Ω) m ∧
          R.b=CollarRevision.capRight (project Ω flow '' Ω) m ∧ R.γ=horizontalSeed (midheight Ω) ∧ R.w=(P^K)⁻¹*m ∧
          R.b-R.a=max m (horizontalSpan (project Ω flow '' Ω)) ∧ volume R.patch.region ≤ ENNReal.ofReal (P^bPow)*volume R.certificate.certificate.prepared.goodPhysical ∧
          OriginalParabolicReadoutBudget R (P^bPow) 2 K := by
  obtain ⟨e,es,sOut,DOut,C,hCap⟩ := exact_phase_centered_cap_with_budget hDD hQQE hCell hHardt hQE hk (ι:=ι)
    N K s D mPow ratePow compPow Cf normPow packPow sCap DCap nCap
    F.slopeReadout_definable F.rate_definable F.root_definable
  obtain ⟨bPow,hC⟩ := uniform_constant_le_power C
  refine ⟨e,es,sOut,DOut,bPow,?_⟩
  intro P m τ M δ T d₁ c CP cR Λ U B Q labels rep fixed Z p Ω hSub hConn piece hp hMem flow Cap
  have hP := Q.P_ge
  have hP₁ : 1≤P := by linarith
  have hτ : 1≤τ := (one_le_pow₀ hP₁).trans Q.cutoff_lower
  have hm : 1≤m := hτ.trans Q.cutoff_le
  have hPos : 0<τ := by linarith
  have hT : ∃ T',∀ q∈F.E p,|q.1|≤T' ∧ |q.2|≤T' :=
    ⟨T,fun q hq => ⟨by linarith [Z.outer_bounds p q hq,abs_nonneg q.2,abs_nonneg (F.slope p q)],
      by linarith [Z.outer_bounds p q hq,abs_nonneg q.1,abs_nonneg (F.slope p q)]⟩⟩
  obtain ⟨SF,hSC,hSD,hS⟩ := specialize_actual_field_graph BF hBF hBD hBgraph p
  rw [capOrderedCell_fiber] at hS
  obtain ⟨R,ha,hb,hγ,hw,hLen,hArea,H⟩ := hCap hP hm Q.m_upper hPos Q.cutoff_le Q.δ_nonneg Q.δ_le Z.packing.nonnegative Z.U_nonnegative
    Z.B_nonnegative Q.buffer Q.flow_defect Q.cubic_defect
    (Z.outer_open p) (Z.root_smooth p) (Z.slope_smooth p) (Z.rate_smooth p) (Z.retains p) hT (Z.boxes p)
    hSub hConn piece (rep p) fixed flow hMem (fun i hi => Z.fixed_comparison p i (hp hi)) Cap
    SF hSC hSD hS p (F.slope_exact p) (F.rate_exact p) (F.root_exact p) (Z.original_window p) (Z.curvature_window p)

  exact ⟨R,ha,hb,hγ,hw,hLen,hArea.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (hC P hP)) _),{H with constant := ⟨H.constant.1,H.constant.2.trans (hC P hP)⟩}⟩

end

end PaperI.CommonNullAssignment
