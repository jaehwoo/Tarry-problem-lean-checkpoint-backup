import Revision.SignedKernel
import Revision.CapKernel
import PaperILean.Nov18CollarSourceKernels
import PaperILean.CommonNullWholeAssignment
import PaperILean.CommonNullActivePartition
import PaperILean.CommonNullParabolicKernels
import PaperILean.CommonNullRibbonKernels

/-! Paper I I1200–I1217. The phasewise assignment uses the original
indexed labels, the literal Borel route tag, and their common physical
prepared geometry. All quantitative budgets precede the cuts. -/

namespace PaperI.CommonNullAssignment

open Set MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Matrix.L2OpNorm
open PaperI.BoundedCharacteristic PaperI.CorridorBands PaperI.ModerateCorridor
open PaperI.ParabolicCollar PaperI.ShortProjectionCaps PaperII.EndpointRangesWhole
open PaperII.QuarticConnection (tangentFrame)

noncomputable section

def RevisedPieceReadout {k : ℕ} {ι : Type} [DecidableEq ι]
    (F : CoefficientSpace k) (P Λ δ U B : ℝ) (N e rate sizePow K : ℕ)
    (E : Set Plane) (c d v : Plane → ℝ) (keep : Plane → Prop)
    (labels : Finset ι) (rep : ι → Plane) (fixed : ι → Fin 6 → ℝ)
    (route : CertificateRoute) (tag : ℝ × ℝ) (Ω : Set Plane) (m τ : ℝ) : Prop :=
  route=.cap ∨ route=.transverseCollar →
    ∃ e₀≤e, ∃ es≤e, ∃ fmt≤e, ∃ deg≤e,
      ∃ Q : OriginalParabolicBandResult F P Λ δ U B N e₀ es rate fmt deg E c d v keep labels rep fixed route tag,
        OriginalParabolicReadoutBudget Q (P^e) (sizePow+2) K ∧
          volume Q.patch.region ≤ ENNReal.ofReal (P^e)*volume Q.certificate.certificate.prepared.goodPhysical ∧
          (route=.transverseCollar → ∃ a b Γ, τ≤b-a ∧ (∀ t∈Ioo a b, (Γ t,t)∈Ω) ∧
            Q.a=0 ∧ Q.b=flux (transverseResidual Γ d) a b ∧ Q.w=(P^K)⁻¹*m ∧
            (∃ pos, ∃ S : TransverseSeed Γ d a b pos, Q.γ=S.point) ∧
            ((∀ t∈Ioo a b,0<transverseResidual Γ d t) ∨ (∀ t∈Ioo a b,transverseResidual Γ d t<0))) ∧
          (route=.cap → ∃ flow : Plane → ℝ → ℝ,
            (∀ p∈Ω, flow p 0=p.1 ∧ DirectedSolution E d p.2 1 (-τ) τ (flow p)) ∧
            (let I := project Ω flow '' Ω
             Q.a=CollarRevision.capLeft I m ∧ Q.b=CollarRevision.capRight I m ∧
               Q.γ=horizontalSeed (midheight Ω) ∧ Q.w=(P^K)⁻¹*m ∧ Q.b-Q.a=max m (horizontalSpan I) ∧
               ∀ i∈labels, project Ω flow (rep i)∈Icc Q.a Q.b))

def RevisedAssignmentReadout {k : ℕ} {σ ι : Type} [DecidableEq ι]
    {F : OriginalNullFamily k σ} {P δ M T Λ U B d₁ : ℝ}
    {N e rate comp Cf norm rp ap fp pp cp : ℕ}
    {labels : Finset ι} {rep : (NullScalarParameters k σ → ℝ) → ι → Plane} {fixed : ι → Fin 6 → ℝ}
    {X : OriginalNullModelInput F P δ M T Λ U B rate comp Cf norm rp ap fp pp labels rep fixed}
    (R : OriginalCommonNullAssignment F P δ M T Λ U B d₁ N e rate comp Cf norm rp ap fp pp cp labels rep fixed X)
    (sizePow K : ℕ) (m τ : ℝ) : Prop :=
  ∀ p j, (R.piece p j).Nonempty →
    (heightSpan (CorridorBands.planeFiber (actualBandFamily R.bands T j) p)<τ → R.route j p=.cap) ∧ RevisedPieceReadout (p ∘ Sum.inl) P Λ δ U B N e rate sizePow K
    (F.E p) (F.root p) (F.slope p) (F.rate p) (F.retains p) (R.piece p j) (rep p) fixed (R.route j p) (R.tag j p) (CorridorBands.planeFiber (actualBandFamily R.bands T j) p) m τ

private theorem actual_slot_subset {α : Type} {A : SideGraph α}
    {B : CertificateBandTemplate (α ⊕ Unit)} {V : ℕ} (prov : BandedSlotProvenance (scaleBoxFamily A) B V)
    (T : ℝ) (p : α → ℝ) (j : Fin B.count) :
    CorridorBands.planeFiber (actualBandFamily B T j) p⊆CorridorBands.planeFiber A p := by
  intro q hq
  rw [actualBandFamily_fiber,prov.exact_slot] at hq
  have h := rankedFiberCell_subset (scaleBoxFamily A) (prov.slot j).1.val (prov.slot j).2 hq.1
  exact h.1

private theorem signed_corridor_seed_subset {C E : Set Plane} {d : Plane → ℝ}
    {ws c CP τ T U : ℝ} (W : ActualBandedCorridor C E d ws c CP τ T U) :
    graphArc W.a W.b (corridorMid W.left W.right)⊆C := by
  rintro ⟨y,z⟩ ⟨hz,hy⟩
  rw [W.represented]
  refine ⟨hz,?_⟩
  have h := W.geometry.sides_lt z hz
  change W.left z<y ∧ y<W.right z
  change y=(W.left z+W.right z)/2 at hy
  exact ⟨by linarith,by linarith⟩

private theorem first_horizontal_bound {f : Plane → ℝ} {q : Plane}
    (hf : DifferentiableAt ℝ f q) :
    HasDerivAt (fun y => f (y,q.2)) (fderiv ℝ f q (1,0)) q.1 := by
  have h : HasDerivAt (fun y => (y,q.2)) ((1,0) : Plane) q.1 :=
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq q.1 h (by cases q; rfl)

theorem revised_common_null_assignment
    (hDD : PublishedEquispacedDividedDifferenceMeanValue) (hQQE : PublishedQuantitativeRealQE)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity) (hPiece : PublishedPiecewiseNashExtensions)
    {k : ℕ} (hk : 1≤k) {σ ι : Type} [Fintype σ] [DecidableEq ι]
    (F : OriginalNullFamily k σ)
    (N K mPow scalePow ratePow widthPow sizePow coordPow compPow Cf normPow rPow aPow fPow packPow : ℕ)
    (C₀ cutPow : ℝ) (hC₀ : 0≤C₀) :
    ∃ e : ℕ, ∀ {P m τ M δ T d₁ c CP cR Λ U B : ℝ},
      OriginalNullScaleInput P m τ M δ T d₁ c CP cR C₀ cutPow K mPow scalePow ratePow widthPow sizePow coordPow →
      ∀ (labels : Finset ι) (rep : (NullScalarParameters k σ → ℝ) → ι → Plane) (fixed : ι → Fin 6 → ℝ)
      (X : OriginalNullModelInput F P δ M T Λ U B ratePow compPow Cf normPow rPow aPow fPow packPow labels rep fixed),
      ∃ R : OriginalCommonNullAssignment F P δ M T Λ U B d₁ N e ratePow compPow Cf normPow rPow aPow fPow packPow coordPow
        labels rep fixed X, RevisedAssignmentReadout R sizePow K m τ := by
  classical
  obtain ⟨V,eI,hIndex⟩ := original_common_band_indices hCell hHardt hQE hPiece (ι:=ι)
    F.core F.outer F.core_format F.slope F.slope_format C₀ cutPow hC₀ ratePow
  obtain ⟨BF,hBF⟩ := F.joint_field_format
  let sf := BF.card
  let df := BF.sup MvPolynomial.totalDegree
  have hfDeg (q : MvPolynomial (NullScalarParameters k σ ⊕ Fin 4) ℝ) (hq : q∈BF) : q.totalDegree≤df :=
    Finset.le_sup hq
  obtain ⟨sCap,DCap,nCap,hSelect⟩ := original_band_phasewise_route_selection hQQE hCell hHardt hQE
    (A:=F.core) (ι:=ι) F.outer_definable F.slope F.rate (hasPolynomialSignDescription_definable F.slope_format)
    F.cap_slope_definable sf df K BF le_rfl hfDeg hBF
  obtain ⟨eC,eCS,sC,dC,cpC,hCap⟩ := exact_cap_kernel hDD hQQE hCell hHardt hQE hk (ι:=ι) F
    N K mPow scalePow ratePow widthPow sizePow coordPow compPow Cf normPow rPow aPow fPow packPow
    C₀ cutPow sf df sCap DCap nCap BF le_rfl hfDeg hBF
  obtain ⟨sSeed,dSeed,hSeedFmt⟩ := original_precut_seed_sign_budget hQE F.core_format F.precutField_definable V
  let S (j : Fin V × Bool) := RankedFiberCell (scaleBoxFamily F.core) j.1.val j.2
  have hS (j : Fin V × Bool) : NullDefinable (S j) :=
    pre_cut_scaled_slot_formats hQE F.core F.core_format j.1.val j.2
  let M (j : Fin V × Bool) := rawSlotMidpoint (S j)
  let RM (j : Fin V × Bool) := asScalarGraph (M j)
  let RA (j : Fin V × Bool) := asScalarGraph (residualGraph (RM j) (CorridorBands.fieldGraph (enlargeField F.slope)))
  have hM (j : Fin V × Bool) : NullDefinable (M j) := rawSlotMidpoint_definable (hS j)
  have hRM (j : Fin V × Bool) : NullDefinable (RM j) := asScalarGraph_definable (hM j)
  have hRA (j : Fin V × Bool) : NullDefinable (RA j) :=
    asScalarGraph_definable (residualGraph_definable (hRM j) (enlargeFieldGraph_definable
      (hasPolynomialSignDescription_definable F.slope_format)))
  have hModerate (j : Fin V × Bool) := original_precut_moderate_kernel hDD hCell hHardt hQE hNash hPiece hk (ι:=ι) F
    N K mPow scalePow ratePow widthPow sizePow coordPow compPow Cf normPow rPow aPow fPow packPow C₀ cutPow hC₀
    (scalarEndpointRelation_definable (hS j) false) (scalarEndpointRelation_definable (hS j) true)
  have hNarrow (j : Fin V × Bool) := original_precut_narrow_kernel hDD hCell hHardt hQE hNash hPiece hk (ι:=ι) F
    N K mPow scalePow ratePow widthPow sizePow coordPow compPow Cf normPow rPow aPow fPow packPow C₀ cutPow (hM j)
  have hFlux (j : Fin V × Bool) := revised_signed_kernel hDD hQQE hCell hHardt hQE hk (ι:=ι) F
    N K mPow scalePow ratePow widthPow sizePow coordPow compPow Cf normPow rPow aPow fPow packPow C₀ cutPow sSeed dSeed
    (hRM j) (hRA j)
  choose eM sM dM hModerate using hModerate
  choose eN sN dN hNarrow using hNarrow
  choose eF eFS sF dF cpF hFlux using hFlux
  let slotBudget (j : Fin V × Bool) := eM j+sM j+dM j+eN j+sN j+dN j+eF j+eFS j+sF j+dF j+cpF j
  let e := eI+eC+eCS+sC+dC+cpC+Finset.univ.sup slotBudget
  have hBudget (j : Fin V × Bool) : slotBudget j≤e := by
    have h := Finset.le_sup (f:=slotBudget) (Finset.mem_univ j)
    dsimp [e]
    omega
  refine ⟨e,?_⟩
  intro P m τ Mbuf δ T d₁ c CP cR Λ U B Q labels rep fixed X
  have hP := Q.P_ge
  have hP₁ : 1≤P := by linarith
  have hτ : 1≤τ := (one_le_pow₀ hP₁).trans Q.cutoff_lower
  have hm : 1≤m := hτ.trans Q.cutoff_le
  have hτ₀ : 0<τ := by linarith
  have hM : 1≤Mbuf := by linarith [Q.buffer]
  have hM₀ : 0<Mbuf := by linarith
  have hCore (p : NullScalarParameters k σ → ℝ) : F.A p⊆F.E p :=
    fun q hq => X.closure_outer hM₀ p (subset_closure hq)
  have hCoreSz (p : NullScalarParameters k σ → ℝ) (q : Plane) (hq : q∈F.A p) :=
    X.outer_bounds p q (hCore p hq)
  have hCoreZ (p : NullScalarParameters k σ → ℝ) (q : Plane) (hq : q∈F.A p) : |q.2|≤T :=
    by linarith [hCoreSz p q hq,abs_nonneg q.1,abs_nonneg (F.slope p q)]
  have hOuter (p : NullScalarParameters k σ → ℝ) : ∃ R,∀ q∈F.E p,|q.1|≤R ∧ |q.2|≤R :=
    ⟨T,fun q hq => ⟨by linarith [X.outer_bounds p q hq,abs_nonneg q.2,abs_nonneg (F.slope p q)],
      by linarith [X.outer_bounds p q hq,abs_nonneg q.1,abs_nonneg (F.slope p q)]⟩⟩
  have hDeriv (p : NullScalarParameters k σ → ℝ) (q : Plane) (hq : q∈F.A p) : ∃ u : ℝ,
      HasDerivAt (fun y => F.slope p (y,q.2)) u q.1 ∧ |u|≤P^ratePow := by
    obtain ⟨hd,hu,_⟩ := X.original_rates hP₁ Q.δ_le p q hq
    exact ⟨uRate (F.slope p) q,first_horizontal_bound hd,hu⟩
  obtain ⟨bands,⟨prov⟩,hCount,hShape,_,_⟩ := hIndex hP hτ Q.low_pos Q.low_upper Q.high_lower Q.T_lower Q.cuts
    (∅ : Finset ι) rep X.rep_measurable (by simp) hCoreSz (X.buffer_one hM) (fun p => (X.slope_smooth p).continuousOn)
    hDeriv
  obtain ⟨piece,hPart,hMeas,hSub,hRep,hFirst,hInv⟩ := original_active_index_partition F X bands
    (fun p => (hShape p).exact)
  let ws := widthCutoff P τ C₀
  have hws : 0<ws := mul_pos (Real.rpow_pos_of_pos (by linarith) _) hτ₀
  have hwsτ : ws≤τ := by
    change P^(-C₀)*τ≤τ
    exact mul_le_of_le_one_left hτ₀.le (Real.rpow_le_one_of_one_le_of_nonpos hP₁ (by linarith))
  have hAll := hSelect bands prov (narrowW:=τ) hP hm hτ₀ Q.cutoff_le Q.cap_width Q.buffer Q.δ_nonneg Q.flow_defect Q.cubic_defect
    hws Q.low_pos Q.low_upper Q.T_lower hShape (X.outer_open) (X.slope_at) hOuter hCoreZ
    (fun p => tangentFrame (F.root p) (F.slope p)) F.retains X.retains X.boxes labels piece rep fixed X.normalize
    (fun p j => (hSub p j).trans (X.active_subset p)) hMeas hRep
    (fun p j i hi => X.normalization_inv p i (hSub p j hi)) (fun p j i hi => X.normalization_norm p i (hSub p j hi))
    (fun p j i hi => X.normalization_eq p i (hSub p j hi)) X.packing
  choose route tag hRouteMeas hTagMeas hTags using hAll
  have hCert (p : NullScalarParameters k σ → ℝ) (j : Fin bands.count) (hActive : (piece p j).Nonempty) :
      Nonempty (OriginalNullBandResult (p ∘ Sum.inl) P Λ δ U B N e ratePow compPow
        (F.E p) (F.root p) (F.slope p) (F.rate p) (F.retains p) (piece p j) (rep p) fixed (route j p) (tag j p)) ∧ RevisedPieceReadout (p ∘ Sum.inl) P Λ δ U B N e ratePow sizePow K
            (F.E p) (F.root p) (F.slope p) (F.rate p) (F.retains p) (piece p j) (rep p) fixed (route j p) (tag j p) (CorridorBands.planeFiber (actualBandFamily bands T j) p) m τ := by
    let C := CorridorBands.planeFiber (actualBandFamily bands T j) p
    let i := prov.slot j
    have hShape' (q : NullScalarParameters k σ → ℝ) :
        CertificateCellShape (CorridorBands.planeFiber (actualBandFamily bands T j) q) (F.E q) (F.slope q)
          ws c CP τ T (P^ratePow) := by
      rw [actualBandFamily_fiber]
      exact (hShape q).certified j
    have hC : C⊆F.A p := actual_slot_subset prov T p j
    have hNZ : C.Nonempty := by
      obtain ⟨l,hl⟩ := hActive
      exact ⟨rep p l,hRep p j l hl⟩
    have hReg := actual_active_band_cases hτ₀ hShape' hNZ
    obtain ⟨flow,hCap',hCapTag,hCorrTag,hArcTag⟩ := hTags j
    have hΛ := X.packing.nonnegative
    have hBudgetI := hBudget i
    have hMτ : τ+3≤Mbuf := by linarith [Q.buffer]
    let activePacking := restrict_original_packing (X.active_subset p) X.packing
    rcases hReg with hShort | ⟨a,b,Γ,k',hab,hLong,hEq,hΓ,hSign,hRes,hKind⟩ | ⟨W,hLong,hL,hR,hKind⟩
    · let q := (⟨p,hShort⟩ : projectionDomain (actualShortFamily (actualBandFamily bands T j) τ))
      have hTag := hCapTag q
      obtain ⟨hr,ht⟩ := hTag
      have hScope := original_short_family_scope hShape' (fun p => actual_slot_subset prov T p j) q
      have hConn : IsConnected C := by
        change IsConnected (CorridorBands.planeFiber (actualBandFamily bands T j) q.val)
        rw [← hScope.1]
        exact hScope.2.2.1
      obtain ⟨CC,ha,hb,hγ,hw,hlen,hArea,hCC⟩ := hCap Q X p hC hConn (piece p j) (hSub p j) (hRep p j) (flow q) (hCap' q)
      rw [hr,ht]
      constructor
      · exact ⟨CC.common hP₁ hΛ (by dsimp [e]; omega) (by dsimp [e]; omega) (by dsimp [e]; omega) (by dsimp [e]; omega)⟩
      · intro _
        refine ⟨_,by dsimp [e]; omega,_,by dsimp [e]; omega,_,by dsimp [e]; omega,_,by dsimp [e]; omega,CC,?_⟩
        constructor
        · exact ⟨⟨hCC.constant.1,hCC.constant.2.trans (pow_le_pow_right₀ hP₁ (by dsimp [e]; omega))⟩,hCC.len,hCC.width,
          hCC.longBound.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP₁ (by omega)) hCC.len.le),
          hCC.widthBound,hCC.seedSmooth,hCC.slopeSmooth,hCC.rateSmooth⟩
        · refine ⟨hArea.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
              (pow_le_pow_right₀ hP₁ (by dsimp [e]; omega))) _),(fun h => nomatch h),?_⟩
          intro _
          have capC := hCap' q
          refine ⟨flow q,fun u hu => (capC.time u hu).2,ha,hb,hγ,hw,hlen,?_⟩
          obtain ⟨hLo,hHi⟩ := CollarRevision.projection_bounded capC hτ₀ (hOuter p)
          have hIncl := (CollarRevision.cap_geometry (hConn.nonempty.image (project C (flow q))) hLo hHi (by linarith : 0≤m)).1
          intro i hi
          rw [ha,hb]
          exact hIncl ⟨rep p i,hRep p j i hi,rfl⟩
    · have hArc : graphArc a b Γ⊆F.A p := hEq ▸ hC
      have hArcrep : ∀ l∈piece p j,rep p l∈graphArc a b Γ := fun l hl => hEq ▸ hRep p j l hl
      have hMd := original_arc_slot_midpoint prov j p hEq
      have hDiff : DifferentiableOn ℝ Γ (Ioo a b) := hΓ.differentiableOn
      have hRead := hArcTag p a b Γ k' hab hEq hDiff hRes
      have hΓBound (z : ℝ) (hz : z∈Ioo a b) : |Γ z|≤T := by
        have hh := hCoreSz p (Γ z,z) (hArc ⟨hz,rfl⟩)
        linarith [abs_nonneg z,abs_nonneg (F.slope p (Γ z,z))]
      rcases hKind with hLow | ⟨pos,hHigh⟩
      · have hLow' (z : ℝ) (hz : z∈Ioo a b) : |transverseResidual Γ (F.slope p) z|≤1 := by
          simpa only [hLow,smallResidual] using hRes z hz
        obtain ⟨Γ',he,hCD,hIn⟩ := literal_narrow_arc_inputs hP Q.cutoff_lower hLong hMτ Q.δ_le
          Q.wpos Q.wupper Q.wInv Q.T_lower (X.outer_bounds p) hΓ hSign hΓBound hLow' hArc
          (X.slope_smooth p).continuousOn (X.boxes p)
        have hMd' : SideReadout (M i) (Sum.elim p (fun _ : Unit => T)) Γ' a b := by
          intro z hz y
          rw [hMd z hz y,he hz]
        obtain ⟨CC⟩ := hNarrow i Q X p hCD hLong hMd' (piece p j) (hSub p j)
          (fun l hl => hIn (hArcrep l hl))
        have hr : route j p=.verticalRibbon := hRead.1.trans
          (by simp [hLow,corridorRoute,not_lt.mpr hLong])
        have ht : tag j p=(lowerDyadicScale (b-a),lowerDyadicScale τ) := by
          simpa only [hLow,corridorRoute,if_neg (not_lt.mpr hLong),certifiedScaleTag] using
            hRead.2 (by simp [hLow,corridorRoute,not_lt.mpr hLong])
        rw [hr,ht]
        constructor
        · exact ⟨CC.common hP₁ hΛ (by dsimp [slotBudget] at hBudgetI; omega)
            (by dsimp [slotBudget] at hBudgetI; omega) (by dsimp [slotBudget] at hBudgetI; omega)⟩
        · intro hr; rcases hr with h|h <;> cases h
      · have hHigh' (z : ℝ) (hz : z∈Ioo a b) : smallResidual (transverseResidual Γ (F.slope p) z) (.high pos) := by
          simpa only [hHigh] using hRes z hz
        obtain ⟨hI,hsign,hEll,hLen,hPC,hBridge⟩ := literal_signed_arc_inputs hP (X.original_model p) activePacking
          hτ Q.cutoff_le hLong Q.size_comparison hΓ hSign hΓBound hArc (X.closure_outer hM₀ p)
          (X.slope_smooth p).continuousOn (hSub p j) hArcrep
          (fun l hl j => (X.fixed_comparison p l hl j).trans (pow_le_pow_right₀ hP₁ (le_max_right ratePow compPow))) hHigh'
        obtain ⟨BF,hBC,hBD,hBS⟩ := hSeedFmt i (Sum.elim p (fun _ : Unit => T)) a b Γ (F.slope p) (F.rate p)
          (F.E p) (hArc.trans (hCore p)) hMd (F.precutField_exact p T)
        have hh : (piece p j).card ≤ P^(fPow*packPow+max rPow aPow+ratePow+9)*Λ*
            (roundedDyadicScale (max m (flux (transverseResidual Γ (F.slope p)) a b))*roundedDyadicScale m) := by
          apply hPC.trans
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP₁ (by omega)) hΛ)
            (mul_nonneg (zero_le_one.trans (one_le_roundedDyadicScale _))
              (zero_le_one.trans (one_le_roundedDyadicScale _)))
        obtain ⟨CC,ha,hb,hw,hSeed,hArea,hCC⟩ := hFlux i Q X p hab hEll hLen hΓ.contDiffOn_of_completeSpace hI hsign hArc hMd
          (original_slot_residual_curve (d:=enlargeField F.slope) hMd hDiff) BF hBC hBD hBS (piece p j) hh hBridge
        have hr : route j p=.transverseCollar := hRead.1.trans
          (by simp [hHigh,corridorRoute,not_lt.mpr hLong])
        have ht : tag j p=(roundedDyadicScale (max m (flux (transverseResidual Γ (F.slope p)) a b)),roundedDyadicScale m) := by
          simpa only [hHigh,corridorRoute,if_neg (not_lt.mpr hLong),certifiedScaleTag] using
            hRead.2 (by simp [hHigh,corridorRoute,not_lt.mpr hLong])
        rw [hr,ht]
        constructor
        · exact ⟨CC.common hP₁ hΛ (by dsimp [slotBudget] at hBudgetI; omega)
            (by dsimp [slotBudget] at hBudgetI; omega) (by dsimp [slotBudget] at hBudgetI; omega)
            (by dsimp [slotBudget] at hBudgetI; omega)⟩
        · intro _
          refine ⟨_,by dsimp [slotBudget] at hBudgetI; omega,_,by dsimp [slotBudget] at hBudgetI; omega,_,by dsimp [slotBudget] at hBudgetI; omega,_,by dsimp [slotBudget] at hBudgetI; omega,CC,?_⟩
          refine ⟨⟨⟨hCC.constant.1,hCC.constant.2.trans (pow_le_pow_right₀ hP₁ (by dsimp [slotBudget] at hBudgetI; omega))⟩,
            hCC.len,hCC.width,hCC.longBound.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP₁ (by omega)) hCC.len.le),
            hCC.widthBound,hCC.seedSmooth,hCC.slopeSmooth,hCC.rateSmooth⟩,?_⟩
          refine ⟨hArea.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
              (pow_le_pow_right₀ hP₁ (by dsimp [slotBudget] at hBudgetI; omega))) _),?_,(fun h => nomatch h)⟩
          intro _
          refine ⟨a,b,Γ,hLong,fun t ht => hEq.symm ▸ (show (Γ t,t)∈graphArc a b Γ from ⟨ht,rfl⟩),ha,hb,hw,⟨pos,hSeed⟩,?_⟩
          cases pos
          · exact Or.inr (fun t ht => (hsign t ht).1)
          · exact Or.inl (fun t ht => (hsign t ht).1)
    · obtain ⟨hLeft,hRight,hMid⟩ := original_band_slot_sides prov j p W.represented W.geometry.sides_lt
      have hRead := hCorrTag p W
      have hFluxCase (hs : (∃ pos,W.index=.small (.high pos)) ∨ (∃ n pos,W.index=.large n (.high pos))) :
          Nonempty (OriginalNullBandResult (p ∘ Sum.inl) P Λ δ U B N e ratePow compPow
            (F.E p) (F.root p) (F.slope p) (F.rate p) (F.retains p) (piece p j) (rep p) fixed (route j p) (tag j p)) ∧ RevisedPieceReadout (p ∘ Sum.inl) P Λ δ U B N e ratePow sizePow K
            (F.E p) (F.root p) (F.slope p) (F.rate p) (F.retains p) (piece p j) (rep p) fixed (route j p) (tag j p) (CorridorBands.planeFiber (actualBandFamily bands T j) p) m τ := by
        let Γ := corridorMid W.left W.right
        have hΓ : ContDiffOn ℝ ∞ Γ (Ioo W.a W.b) :=
          ((hL.contDiffOn_of_completeSpace).add hR.contDiffOn_of_completeSpace).div_const 2
        obtain ⟨pos,hI,hsign,hEll,hLen,hPC,hBridge⟩ := literal_signed_corridor_inputs hP (X.original_model p)
          activePacking W hτ Q.cutoff_le hLong Q.ws_bound Q.high_lower Q.size_comparison hs (hSub p j)
          (hRep p j) (X.fixed_comparison p)
        have hArc := (signed_corridor_seed_subset W).trans hC
        obtain ⟨BF,hBC,hBD,hBS⟩ := hSeedFmt i (Sum.elim p (fun _ : Unit => T)) W.a W.b Γ (F.slope p) (F.rate p)
          (F.E p) (hArc.trans (hCore p)) hMid (F.precutField_exact p T)
        obtain ⟨CC,ha,hb,hw,hSeed,hArea,hCC⟩ := hFlux i Q X p W.geometry.hab hEll hLen hΓ hI hsign hArc hMid
          (original_slot_residual_curve (d:=enlargeField F.slope) hMid (hΓ.differentiableOn (by simp))) BF hBC hBD hBS
          (piece p j) hPC hBridge
        have hs' : corridorRoute τ (W.b-W.a) W.index=.transverseCollar := by
          rcases hs with ⟨s,he⟩ | ⟨n,s,he⟩ <;> simp [he,corridorRoute,not_lt.mpr hLong]
        have hr := hRead.1.trans hs'
        have ht := hRead.2 (by rw [hs']; decide)
        simp only [hs',certifiedScaleTag] at ht
        rw [hr,ht]
        constructor
        · exact ⟨CC.common hP₁ hΛ (by dsimp [slotBudget] at hBudgetI; omega)
            (by dsimp [slotBudget] at hBudgetI; omega) (by dsimp [slotBudget] at hBudgetI; omega)
            (by dsimp [slotBudget] at hBudgetI; omega)⟩
        · intro _
          refine ⟨_,by dsimp [slotBudget] at hBudgetI; omega,_,by dsimp [slotBudget] at hBudgetI; omega,_,by dsimp [slotBudget] at hBudgetI; omega,_,by dsimp [slotBudget] at hBudgetI; omega,CC,?_⟩
          refine ⟨⟨⟨hCC.constant.1,hCC.constant.2.trans (pow_le_pow_right₀ hP₁ (by dsimp [slotBudget] at hBudgetI; omega))⟩,
            hCC.len,hCC.width,hCC.longBound.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP₁ (by omega)) hCC.len.le),
            hCC.widthBound,hCC.seedSmooth,hCC.slopeSmooth,hCC.rateSmooth⟩,?_⟩
          refine ⟨hArea.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
              (pow_le_pow_right₀ hP₁ (by dsimp [slotBudget] at hBudgetI; omega))) _),?_,(fun h => nomatch h)⟩
          intro _
          refine ⟨W.a,W.b,Γ,hLong,fun t ht => signed_corridor_seed_subset W ⟨ht,rfl⟩,ha,hb,hw,⟨pos,hSeed⟩,?_⟩
          cases pos
          · exact Or.inr (fun t ht => (hsign t ht).1)
          · exact Or.inl (fun t ht => (hsign t ht).1)
      rcases hKind with hs | hLow | hs | hMed
      · exact hFluxCase (Or.inl hs)
      · obtain ⟨hCD,hC'⟩ := literal_narrow_corridor_inputs W hLow hP Q.cutoff_lower hLong hwsτ hMτ Q.δ_le
          Q.wpos Q.wupper Q.wInv Q.T_lower (X.outer_bounds p) hC (X.slope_smooth p).continuousOn (X.boxes p)
        obtain ⟨CC⟩ := hNarrow i Q X p hCD hLong hMid (piece p j) (hSub p j) (fun l hl => hC' (hRep p j l hl))
        have hr := hRead.1.trans (by simp [hLow,corridorRoute,not_lt.mpr hLong] :
          corridorRoute τ (W.b-W.a) W.index=.verticalRibbon)
        have ht := hRead.2 (by simp [hLow,corridorRoute,not_lt.mpr hLong])
        simp only [hLow,corridorRoute,if_neg (not_lt.mpr hLong),certifiedScaleTag] at ht
        rw [hr,ht]
        constructor
        · exact ⟨CC.common hP₁ hΛ (by dsimp [slotBudget] at hBudgetI; omega)
            (by dsimp [slotBudget] at hBudgetI; omega) (by dsimp [slotBudget] at hBudgetI; omega)⟩
        · intro hr; rcases hr with h|h <;> cases h
      · exact hFluxCase (Or.inr hs)
      · obtain ⟨CC⟩ := hModerate i Q X p W hLong hMed hC hLeft hRight (piece p j) (hSub p j) (hRep p j)
        have hRte : corridorRoute τ (W.b-W.a) W.index=.moderateRibbon := by
          obtain ⟨n,j,he,hn⟩ := hMed
          cases j with
          | low => simp [he,corridorRoute,not_lt.mpr hLong]
          | medium => simp [he,corridorRoute,not_lt.mpr hLong]
          | high pos => exact (hn pos rfl).elim
        have hr := hRead.1.trans hRte
        have ht := hRead.2 (by rw [hRte]; decide)
        simp only [hRte,certifiedScaleTag] at ht
        rw [hr,ht]
        constructor
        · exact ⟨CC.common hP₁ hΛ (by dsimp [slotBudget] at hBudgetI; omega)
            (by dsimp [slotBudget] at hBudgetI; omega) (by dsimp [slotBudget] at hBudgetI; omega)⟩
        · intro hr; rcases hr with h|h <;> cases h
  have he : eI≤e := by dsimp [e]; omega
  have hT₁ : (1:ℝ)≤T := by linarith [Q.T_lower]
  have hLog₁ : 1≤1+Real.log T := by linarith [Real.log_nonneg hT₁]
  have hC : (bands.count : ℝ)≤P^e*(1+Real.log T)^e :=
    hCount.trans (mul_le_mul (pow_le_pow_right₀ hP₁ he) (pow_le_pow_right₀ hLog₁ he) (by positivity) (by positivity))
  have hScale (p : NullScalarParameters k σ → ℝ) (j : Fin bands.count)
      (hj : j∈Finset.univ.filter (fun j => (piece p j).Nonempty)) : 1≤(tag j p).1 ∧ 1≤(tag j p).2 := by
    obtain ⟨C⟩ := (hCert p j (Finset.mem_filter.mp hj).2).1
    rw [← C.tag_eq]
    exact ⟨C.scale.L_one,C.scale.W_one⟩
  refine ⟨⟨bands,piece,route,tag,hPart,hFirst,hMeas,hRouteMeas,hTagMeas,hC,fun p j h => (hCert p j h).1,?_,?_⟩,?_⟩
  · intro p η hη
    let active := (Finset.univ : Finset (Fin bands.count)).filter (fun j => (piece p j).Nonempty)
    have hActiveCard : (active.card : ℝ)≤bands.count := by
      have hc := Finset.card_filter_le (s := (Finset.univ : Finset (Fin bands.count)))
        (fun j => (piece p j).Nonempty)
      exact_mod_cast (show active.card≤bands.count by simpa [active] using hc)
    exact (inverse_area_sum _ (fun j => (tag j p).1) (fun j => (tag j p).2) hη
      (fun j hj => (hScale p j hj).1) (fun j hj => (hScale p j hj).2)).trans
      (hActiveCard.trans hC)
  · exact rq_window_log_bound hP Q.T_lower ((one_le_inv₀ Q.d1_pos).mpr Q.d1_le) Q.rq_bound

  · intro p j hj
    refine ⟨?_,(hCert p j hj).2⟩
    change heightSpan (CorridorBands.planeFiber (actualBandFamily bands T j) p)<τ → route j p=.cap
    intro hshort
    obtain ⟨i,hi⟩ := hj
    have hNZ := hRep p j i hi
    have shape (q : NullScalarParameters k σ → ℝ) :
        CertificateCellShape (CorridorBands.planeFiber (actualBandFamily bands T j) q) (F.E q) (F.slope q)
          ws c CP τ T (P^ratePow) := by
      rw [actualBandFamily_fiber]
      exact (hShape q).certified j
    have hs := (actual_short_branch_domain_iff shape p).mpr ⟨⟨_,hNZ⟩,hshort⟩
    obtain ⟨_,_,hRoute,_,_⟩ := hTags j
    exact (hRoute ⟨p,hs⟩).1

end

end PaperI.CommonNullAssignment
