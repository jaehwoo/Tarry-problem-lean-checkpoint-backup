import PaperILean.CommonNullLongCollar
import PaperILean.CommonNullCollarTail
import PaperILean.CommonNullRibbonPrepared

/-! The actual long-collar assignment.  The geometric input is the
original signed graph, the long flux and the supplied buffered core. -/

namespace PaperI.CommonNullAssignment

open Set FirstOrder MeasureTheory Filter
open scoped ContDiff ENNReal Topology
open PaperI.BoundedCharacteristic PaperI.CorridorBands PaperI.ShortProjectionCaps
open PaperI.GoodStrips PaperI.Preparation PaperI.ParabolicCollar PaperII.EndpointRangesWhole
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

noncomputable section

private abbrev RD {σ : Type} (G : Set (σ → ℝ)) := (univ : Set ℝ).Definable Language.ring G

private theorem mixedJet_congr_open {U : Set Plane} (ho : IsOpen U)
    {f g : Plane → ℝ} (hEq : EqOn f g U) (i j : ℕ) : EqOn (mixedJet f i j) (mixedJet g i j) U := by
  have stepX {a b : Plane → ℝ} (h : EqOn a b U) : EqOn (derivX a) (derivX b) U := by
    intro q hq
    have hc : Continuous (fun r : ℝ => (r,q.2)) := continuous_id.prodMk continuous_const
    have hS : ∀ᶠ r in 𝓝 q.1, (r,q.2)∈U := hc.continuousAt (ho.mem_nhds (by simpa only [Prod.mk.eta] using hq))
    have hE : (fun r => a (r,q.2)) =ᶠ[𝓝 q.1] (fun r => b (r,q.2)) := hS.mono (fun _ hx => h hx)
    exact hE.deriv_eq
  have stepY {a b : Plane → ℝ} (h : EqOn a b U) : EqOn (derivY a) (derivY b) U := by
    intro q hq
    have hc : Continuous (fun r : ℝ => (q.1,r)) := continuous_const.prodMk continuous_id
    have hS : ∀ᶠ r in 𝓝 q.2, (q.1,r)∈U := hc.continuousAt (ho.mem_nhds (by simpa only [Prod.mk.eta] using hq))
    have hE : (fun r => a (q.1,r)) =ᶠ[𝓝 q.2] (fun r => b (q.1,r)) := hS.mono (fun _ hx => h hx)
    exact hE.deriv_eq
  have hX (n : ℕ) : EqOn (horizontalJet f n) (horizontalJet g n) U := by
    induction n with
    | zero => exact hEq
    | succ n ih => rw [horizontalJet_succ,horizontalJet_succ]; exact stepX ih
  induction j with
  | zero => exact hX i
  | succ j ih => rw [mixedJet_succ_right,mixedJet_succ_right]; exact stepY ih

theorem prepare_collar_with_polynomial_bridge
    (hDD : PublishedEquispacedDividedDifferenceMeanValue) (hQQE : PublishedQuantitativeRealQE)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) {σ ι κ : Type} [Finite σ] [DecidableEq ι] [Fintype κ]
    (N K s D sizePow ratePow fixedPow boundPow packPow : ℕ)
    (Jf : κ → Set ((σ ⊕ Fin 3) → ℝ)) (Ja : Set ((σ ⊕ Fin 3) → ℝ))
    (hJf : ∀ i,RD (Jf i)) (hJa : RD Ja) :
    ∃ e : ℕ, ∀ {P m δ M Λ : ℝ}, 2≤P → 1≤m → 0≤δ → δ≤1 → 0≤Λ → 4*m<M →
      (P^ratePow*δ)*(2*m)≤Real.log 2 → (P^ratePow*δ)*m^3≤1/16 →
      ∀ {a b : ℝ} {Γ : ℝ → ℝ} {d v c : Plane → ℝ} {pos : Bool} {A E : Set Plane}
      {retained : Plane → Prop} {frame : Plane → Fin 6 → ℝ},
      let w := (P^K)⁻¹*m
      let α := transverseResidual Γ d
      let ell := flux α a b
      let L := roundedDyadicScale (max m ell)
      let W := roundedDyadicScale m
      let R := Ioo a b ×ˢ Ioo (-w) w
      a<b → 1≤ell → max m ell≤P^sizePow*ell → ContDiffOn ℝ ∞ Γ (Ioo a b) →
      IntervalIntegrable α volume a b → ContDiffOn ℝ ∞ α (Ioo a b) →
      (∀ z∈Ioo a b,residualSign (α z) pos ∧ 1≤|α z|) →
      (∀ q∈E,retained q) → (∀ q∈A,CertifiedBox P δ M ratePow fixedPow E d v frame q) →
      graphArc a b Γ ⊆ A →
      ∀ (p : σ → ℝ) (F : κ → Plane → ℝ) (B : κ → ℝ),
      (∀ i,0≤B i) →
      (∀ i,ContDiffOn ℝ ∞ (fun q => F i (parabolicEval (fun z => (Γ z,z)) d v q)) R) →
      (∀ i,RealizesOn (Jf i) p (fun q => F i (parabolicEval (fun z => (Γ z,z)) d v q)) R) →
      RealizesOn Ja p (fun q => α q.1) R →
      (∀ i q,q∈R → |F i (parabolicEval (fun z => (Γ z,z)) d v q)|≤B i) →
      ∀ (seedFormat : Finset (MvPolynomial (Unit ⊕ Fin 4) ℝ)),seedFormat.card≤s →
      (∀ q∈seedFormat,q.totalDegree≤D) →
      PolynomialSignDetermined seedFormat (originalSeedGraph a b (fun z => (Γ z,z)) d v) →
      ∀ (labels : Finset ι) (rep : ι → Plane) (fixed : ι → Fin 6 → ℝ),
      (labels.card : ℝ)≤P^packPow*Λ*(L*W) →
      (∀ i∈labels,(rep i).2∈Ioo a b ∧ |Γ (rep i).2-(rep i).1|≤P^boundPow*L ∧
        |d (Γ (rep i).2,(rep i).2)-d (rep i)|≤P^boundPow*L ∧
        IntrinsicReach E d (rep i) (Γ (rep i).2,(rep i).2) (3*(P^boundPow*L)) ∧
        ∀ j,|fixedEndpointFrame (fixed i) c d (rep i) j|≤P^boundPow) →
      Nonempty (LongCollarResult Γ a b m w P Λ c d v pos N e E retained F B labels rep fixed) := by
  obtain ⟨sOut,DOut,n,hGeom⟩ := transverse_collar_of_signed_graph hQQE hCell hHardt hQE s D K
  obtain ⟨C,hC,hPrepare⟩ := prepare_transverse_collar_fields hDD hCell hHardt hQE N Jf Ja hJf hJa
  obtain ⟨q,hQ⟩ := uniform_constant_le_power (max 50 (max C (max 9 (8*n))))
  let rate := max ratePow boundPow
  let e := q+2*rate+K+sizePow+packPow+boundPow+1
  refine ⟨e,?_⟩
  intro P m δ M Λ hP hm hδ hδ₁ hΛ hM hSmall hSmall₃ a b Γ d v c pos A E retained frame
  dsimp only
  intro hab hEll hLong hΓ hI hα hsign hRetain hBoxes hSeed p F B hB hSM hGraph hGa hAmp
    seedFormat hScard hSD hS labels rep fixed hCount hRep
  let α := transverseResidual Γ d
  let ell := flux α a b
  let L := roundedDyadicScale (max m ell)
  let W := roundedDyadicScale m
  let w := (P^K)⁻¹*m
  let R := Ioo a b ×ˢ Ioo (-w) w
  let A₀ := P^rate
  have hP₁ : 1≤P := by linarith
  have hP₀ : 0<P := by linarith
  have hp (i : ℕ) : 0<P^i := pow_pos hP₀ _
  have hA₀ : 1≤A₀ := one_le_pow₀ hP₁
  have hW : 0<w := by dsimp [w]; positivity
  have hwcap : (P^K)⁻¹≤1 := inv_le_one_of_one_le₀ (one_le_pow₀ hP₁)
  have hwm : w≤m := by dsimp [w]; nlinarith only [mul_le_mul_of_nonneg_right hwcap (show 0≤m by linarith)]
  have hL : 1≤L := one_le_roundedDyadicScale _
  have hml : m≤L := (le_max_left _ _).trans (le_roundedDyadicScale _)
  have heL : ell≤L := (le_max_right _ _).trans (le_roundedDyadicScale _)
  have hRate : P^ratePow≤A₀ := pow_le_pow_right₀ hP₁ (le_max_left ..)
  have hFix : P^boundPow≤A₀ := pow_le_pow_right₀ hP₁ (le_max_right ..)
  have hT : ∀ z∈Ioo a b, residualSign (α z) pos := fun z hz => (hsign z hz).1
  obtain ⟨S⟩ := exists_actual_transverse_seed hab
    (fun z hz => (hΓ.contDiffAt (isOpen_Ioo.mem_nhds hz)).differentiableAt (by simp))
    hI hα.continuousOn hT (fun z hz => (hsign z hz).2)
  obtain ⟨V⟩ := hGeom hP hm hδ (inv_pos.mpr (hp K)) hwcap le_rfl hM ratePow fixedPow hSmall₃
    hRetain hBoxes hSeed S (by linarith) seedFormat hScard hSD hS
  let f i := fun x => F i (parabolicEval (fun z => (Γ z,z)) d v x)
  obtain ⟨G,hGm,hGR,hIm,hGA,hJets⟩ := hPrepare p S hI hα hT (by linarith) hW f B hSM hGraph hGa hAmp
    V.differential n V.derivative V.det_lower V.multiplicity
  have hSeedIn (s : ℝ) (hs : s∈Ioo 0 ell) : S.point s∈A := by
    rw [S.original_height s hs]
    have hx := S.clock.val.map_target (show s∈S.clock.val.target by rw [S.clock.property.2.1]; exact hs)
    exact hSeed ⟨by simpa only [S.clock.property.1] using hx,rfl⟩
  let patch : NullPatch d v := .transverseCollar S.point 0 ell w
  let Scale := roundedNullScale (max m ell) m (le_max_left _ _)
  let I := parabolicEval S.point d v '' G
  have hInside : patch.region⊆E := by
    rintro _ ⟨x,hx,rfl⟩
    exact (V.inside x hx).1
  have hIin : I ⊆ patch.region := by
    rintro z ⟨x,hx,rfl⟩
    exact ⟨![x.1,x.2],hGR hx,rfl⟩
  have hK : ∀ p∈patch.region, retained p := fun p hp => hRetain p (hInside hp)
  have hIeq : I = patch.evalAt '' G := rfl
  have hLive : volume I ≠ ⊤ := by
    obtain ⟨hImage,_,_,hUp⟩ := flux_rectangle_image_area _ 0 ell w (by linarith)
      V.differential V.derivative (fun x hx => ⟨V.det_lower x hx,V.det_upper x hx⟩) n V.multiplicity
    have hsub : I ⊆ (MeasurableEquiv.finTwoArrow : Coordinates ≃ᵐ Plane) ''
        (collarMap S.point d v '' fluxRectangle 0 ell w) := by
      rintro p ⟨x,hx,rfl⟩
      exact ⟨collarMap S.point d v ![x.1,x.2],⟨![x.1,x.2],hGR hx,rfl⟩,rfl⟩
    let pl : Coordinates ≃ᵐ Plane := MeasurableEquiv.finTwoArrow
    let Q := collarMap S.point d v '' fluxRectangle 0 ell w
    have hQm := pl.measurableEmbedding.measurableSet_image.mpr hImage
    have hVol := (volume_preserving_finTwoArrow ℝ).measure_preimage hQm.nullMeasurableSet
    change volume (pl ⁻¹' (pl '' Q)) = volume (pl '' Q) at hVol
    rw [preimage_image_eq _ pl.injective] at hVol
    exact ne_top_of_le_ne_top (by rw [← hVol]; exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hUp)
      (measure_mono hsub)
  have hQ' := hQ P hP
  have hPq : C≤P^q ∧ 9≤P^q ∧ 50≤P^q ∧ 8*(n:ℝ)≤P^q := by
    exact ⟨(le_max_left _ _).trans ((le_max_right _ _).trans hQ'),
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hQ')),
      (le_max_left _ _).trans hQ',
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hQ'))⟩
  have hCompare : (P^e)⁻¹*Scale.S ≤ volume.real I := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top n)) hLive) hGA
    simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofNat] at h
    rw [ENNReal.toReal_ofReal (mul_nonneg (by linarith : 0≤ell) hW.le)] at h
    have hLL : L≤2*max m ell := (roundedDyadicScale_lt_two_max _).le.trans_eq
      (congrArg (2*·) (max_eq_right (hm.trans (le_max_left _ _))))
    have hWW : W≤2*m := (roundedDyadicScale_lt_two_max _).le.trans_eq
      (congrArg (2*·) (max_eq_right hm))
    have hS : Scale.S≤4*P^sizePow*(m*ell) := by
      change L*W≤_
      calc
        _ ≤ (2*max m ell)*(2*m) := mul_le_mul hLL hWW
          (zero_le_one.trans (one_le_roundedDyadicScale m)) (by positivity)
        _ ≤ (2*(P^sizePow*ell))*(2*m) := by gcongr
        _ = _ := by ring
    have hEq : m=(P^K)*w := by dsimp [w]; rw [←mul_assoc,mul_inv_cancel₀ (hp _).ne',one_mul]
    have hPow : (8*(n:ℝ))*P^(K+sizePow)≤P^e := by
      calc
        _ ≤ P^q*P^(K+sizePow) := mul_le_mul_of_nonneg_right hPq.2.2.2 (hp _).le
        _ = P^(q+(K+sizePow)) := (pow_add _ _ _).symm
        _ ≤ _ := pow_le_pow_right₀ hP₁ (by dsimp [e]; omega)
    have hmI : 0≤volume.real I := ENNReal.toReal_nonneg
    apply (inv_mul_le_iff₀ (hp e)).2
    calc
      _ ≤ 4*P^sizePow*(m*ell) := hS
      _ = 4*P^(K+sizePow)*(ell*w) := by rw [hEq,pow_add]; ring
      _ ≤ 4*P^(K+sizePow)*(2*n*volume.real I) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = ((8*(n:ℝ))*P^(K+sizePow))*volume.real I := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hPow hmI
  have hPull (i : κ) : EqOn (fluxPush S.clock.val.symm (f i)) (F i ∘ patch.evalAt) (Ioo 0 ell ×ˢ Ioo (-w) w) := by
    intro x hx
    have he := S.original_height x.1 hx.1
    unfold fluxPush
    change F i (parabolicEval (fun z => (Γ z,z)) d v (S.clock.val.symm x.1,x.2)) =
      F i (parabolicEval S.point d v x)
    unfold parabolicEval collarPoint collarMap
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,he]
  have hLongExp : C≤P^e ∧ 9≤P^e ∧ 50*A₀^2≤P^e ∧ P^packPow≤P^e := by
    have he₁ := pow_le_pow_right₀ hP₁ (show q≤e by dsimp [e]; omega)
    refine ⟨hPq.1.trans he₁,hPq.2.1.trans he₁,?_,pow_le_pow_right₀ hP₁ (by dsimp [e]; omega)⟩
    calc
      _ ≤ P^q*A₀^2 := mul_le_mul_of_nonneg_right hPq.2.2.1 (sq_nonneg _)
      _ = P^(q+2*rate) := by simp only [A₀,pow_add,pow_mul,Nat.mul_comm 2 rate]
      _ ≤ _ := pow_le_pow_right₀ hP₁ (by dsimp [e]; omega)
  let prep : PreparedPhysicalPatch d v N P e E retained Scale F B :=
    ⟨patch,hInside,hK,G,hGm,hGR,I,hIeq,hIm,hIin,hCompare,ell,2*w,by linarith,by linarith,
      fun x hx i j k hj => by
        rw [← mixedJet_congr_open (isOpen_Ioo.prod isOpen_Ioo) (hPull i) j k (hGR hx)]
        exact (hJets x hx i j k hj).trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hLongExp.1 (hB i)) (by positivity))⟩
  have hField (s : ℝ) (hs : s∈Ioo 0 ell) :=
    let bb := hBoxes (S.point s) (hSeedIn s hs)
    bb.small_rates (S.point s) bb.mem_carrier
  have hSlope (s t : ℝ) (hs : s∈Ioo 0 ell) (ht : t∈Ioo (-w) w) :
      |d (S.point s)+v (S.point s)*t-d (parabolicEval S.point d v (s,t))| ≤ 1 := by
    have ht' : |t|≤m := (abs_le.mpr ⟨ht.1.le,ht.2.le⟩).trans hwm
    obtain ⟨_,hh⟩ := buffered_parabolic_slope_defect (hBoxes _ (hSeedIn s hs)) hP hm hδ hSmall hSmall₃ hM ht'
    have hb : (P^ratePow*δ)*|t|^3≤1/16 := (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) ht' 3) (by positivity)).trans hSmall₃
    have hB₀ : (P^ratePow*δ)≤1 := by
      have hh' := mul_le_mul_of_nonneg_left (one_le_pow₀ hm (n:=3)) (show 0≤P^ratePow*δ by positivity)
      linarith only [hh',hSmall₃]
    have hB₂ : (P^ratePow*δ)*|t|^2≤1/16 := by
      apply le_trans _ hSmall₃
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ m^2 := pow_le_pow_left₀ (abs_nonneg _) ht' _
        _ ≤ m^3 := by nlinarith only [mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hm)]
    have hB₃ := (mul_le_mul_of_nonneg_right hB₀
      (show 0≤(P^ratePow*δ)*|t|^3 by positivity)).trans (by simpa only [one_mul] using hb)
    change _ ≤ _ at hh
    change _ ≤ _
    simpa only [parabolicEval,collarPoint,collarMap,Matrix.cons_val_zero,Matrix.cons_val_one] using
      (show |d (S.point s)+v (S.point s)*t-d ((S.point s).1+d (S.point s)*t+v (S.point s)*t^2/2,(S.point s).2+t)|≤1 by
        nlinarith only [hh,hB₂,hB₃])
  have hReach (i : ι) (hi : i∈labels) (p : Plane) (hp' : p∈patch.region) :
      IntrinsicReach E d (rep i) p (P^e*L) := by
    obtain ⟨x,hx,rfl⟩ := hp'
    let u := S.clock.val (rep i).2
    have hu : u∈Ioo 0 ell := by
      have ht' := S.clock.val.map_source (show (rep i).2∈S.clock.val.source by rw [S.clock.property.1]; exact (hRep i hi).1)
      simpa only [u,S.clock.property.2.1] using ht'
    have hb := (hRep i hi).2.2.2.1
    rw [← S.graph _ (hRep i hi).1] at hb
    have hmap (s : ℝ) (hs : s∈Ioo 0 ell) : S.point s∈E :=
      (hBoxes _ (hSeedIn s hs)).carrier_subset (hBoxes _ (hSeedIn s hs)).mem_carrier
    have hLift : L≤P^boundPow*L := le_mul_of_one_le_left (by linarith) (one_le_pow₀ hP₁)
    have hPth := transverse_anchor_to_patch S (fun s hs => hmap s hs) (hΓ.of_le (by simp)) hα.continuousOn hT
      (hL.trans hLift) hW ((hwm.trans hml).trans hLift) (heL.trans hLift) hu hx.1 hb (abs_lt.mpr hx.2)
      (fun t ht => (V.inside ![x 0,t] ⟨hx.1,ht⟩).1) (fun t ht => hSlope (x 0) t hx.1 ht)
    have he : ![x 0,x 1]=x := by ext j; fin_cases j <;> rfl
    rw [he] at hPth
    apply hPth.mono
    have h9 : (9:ℝ) ≤ P^q := hPq.2.1
    calc
      _ = (9*P^boundPow)*L := by ring
      _ ≤ (P^q*P^boundPow)*L := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h9 (hp _).le) (by linarith)
      _ ≤ _ := by rw [←pow_add]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP₁ (by dsimp [e]; omega)) (by linarith)
  have hFixed (i : ι) (hi : i∈labels) (p : Plane) (hp' : p∈patch.region) :
      let g := fixedEndpointFrame (fixed i) c d p
      |g 5|≤P^e*L ∧ |g 3|≤P^e*L ∧ |g 4|+|g 4-g 3*g 5|≤P^e*L^2 := by
    obtain ⟨x,hx,rfl⟩ := hp'
    let u := S.clock.val (rep i).2
    have hu : u∈Ioo 0 ell := by
      have ht' := S.clock.val.map_source (show (rep i).2∈S.clock.val.source by rw [S.clock.property.1]; exact (hRep i hi).1)
      simpa only [u,S.clock.property.2.1] using ht'
    have hb := S.graph _ (hRep i hi).1
    have ht : |x 1|≤L := (abs_le.mpr ⟨hx.2.1.le,hx.2.2.le⟩).trans (hwm.trans hml)
    have hF (r : ℝ) (hr : r∈Ioo 0 ell) : DifferentiableAt ℝ d (S.point r) ∧
        fderiv ℝ d (S.point r) (d (S.point r),1)=v (S.point r) ∧
        |fderiv ℝ d (S.point r) (1,0)|≤A₀ ∧ |v (S.point r)|≤A₀ := by
      obtain ⟨h₁,_,h₃,h₄,_,_,h₇⟩ := hField r hr
      exact ⟨h₁.differentiableAt (by norm_num),h₃,h₄.trans ((mul_le_of_le_one_right (hp _).le hδ₁).trans hRate),
        h₇.trans hRate⟩
    have hD := (hRep i hi).2.2.1.trans (mul_le_mul_of_nonneg_right hFix (by linarith : 0≤L))
    have hZ : |(S.point u).2-(rep i).2|≤L := by rw [hb]; simp; linarith
    have hY : |(S.point u).1-(rep i).1-d (rep i)*((S.point u).2-(rep i).2)|≤A₀*L^2 := by
      rw [hb]
      simp only [sub_self,mul_zero,sub_zero]
      apply ((hRep i hi).2.1).trans
      exact mul_le_mul hFix (by nlinarith only [mul_nonneg (by linarith : 0≤L) (sub_nonneg.mpr hL)]) (by linarith) (by linarith)
    obtain ⟨hF₁,hD₁,hY₁⟩ := anchored_collar_ranges hA₀ hL (by simpa only [sub_zero] using heL)
      ht hu hx.1 S.derivative hF hZ (by rwa [hb]) hY (hSlope (x 0) (x 1) hx.1 hx.2)
    have hRanges := fixed_collar_ranges (c:=c) (fixed:=fixed i) hA₀ hL hF₁ hD₁ hY₁
      (fun j => ((hRep i hi).2.2.2.2 j).trans hFix)
    have hU : 6*A₀≤50*A₀^2 := by
      have h := le_mul_of_one_le_left (show 0≤A₀ by linarith) hA₀
      nlinarith only [h,show 0≤A₀ by linarith]
    have hF' : 4*A₀≤6*A₀ := by linarith
    have hP' := hU.trans hLongExp.2.2.1
    have he : ![x 0,x 1]=x := by ext j; fin_cases j <;> rfl
    rw [he] at hRanges
    exact ⟨hRanges.1.trans (mul_le_mul_of_nonneg_right (hF'.trans hP') (by linarith)),
      hRanges.2.1.trans (mul_le_mul_of_nonneg_right hP' (by linarith)),
      hRanges.2.2.trans (mul_le_mul_of_nonneg_right hLongExp.2.2.1 (sq_nonneg _))⟩
  have hCount' : (labels.card : ℝ)≤P^e*Λ*Scale.S := hCount.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLongExp.2.2.2 hΛ) (zero_le_one.trans Scale.S_one))
  let output : IndexedPreparedPatch d v c N P Λ e E retained Scale F B labels rep fixed :=
    ⟨prep,hCount',hReach,fun i hi => by
      obtain ⟨hV,hEq⟩ := ModerateCorridor.physical_fixed_area (fixed i) c d hIm
      exact ⟨hV,congrArg ENNReal.toReal hEq⟩⟩
  obtain ⟨Cfmt,_,_,hFmt⟩ := V.original_format
  exact ⟨⟨S,Scale,rfl,rfl,output,rfl,hFixed,Cfmt,hFmt⟩⟩

end

end PaperI.CommonNullAssignment
