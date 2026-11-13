import PaperILean.OriginalStripScaleTransfer

/-! I1265: reported lengths are rounded, but the associated strip always
uses the actual width W0. All estimates concern the SAME B family. -/
noncomputable section
namespace PaperI
open Set Metric MeasureTheory

theorem originalComponentParameters_eta {ρ : Type*} (p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ) :
    Sum.elim (Sum.elim (fun r => p (Sum.inl (Sum.inl r)))
      (fun _ : Unit => p (Sum.inl (Sum.inr ())))) (fun _ : Unit => p (Sum.inr ()))=p := by
  funext r
  rcases r with (r | u) | u
  · rfl
  · cases u; rfl
  · cases u; rfl

def OriginalBorelStripFamily.RoundedComponentAt
    {ρ : Type} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (B : OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ))
    (N : ℕ) (Q : ℝ) (p : originalJointPositiveWidthDomain ρ) : Prop :=
  let L0 := originalJointComponentScale D i p.val
  let W0 := p.val (Sum.inr ())
  let L := roundedDyadicScale L0
  let W := roundedDyadicScale W0
  let z := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (B.anchor p)
  let S := B.strip p W0
  1≤Q ∧ 1≤W ∧ W≤L ∧ B.PhysicalPreparedAt N Q L p ∧
    L/Q≤B.right p-B.left p ∧ B.right p-B.left p≤L ∧ W/Q≤W0/4 ∧ W0/4≤W ∧
    ∀ E : Set (WithLp 2 (Fin 2 → ℝ)),
      0≤p.val (Sum.inl (Sum.inr ())) → IsOpen E → Bornology.IsBounded E →
      (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=projectionFiber G (fun r => p.val (Sum.inl (Sum.inl r))) →
      (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox (p.val (Sum.inl (Sum.inr ()))) →
      S⊆E ∧ MeasurableSet S ∧ volume.real S=(B.right p-B.left p)*W0/2 ∧ L*W/Q≤volume.real S ∧
        ∀ a∈bufferedBandComponent E W0 z,
          bufferedBandComponent E W0 z ∪ S⊆closedBall a (2*L) ∧
          volume (relativePlanarEndpoints a (bufferedBandComponent E W0 z ∪ S))≤ENNReal.ofReal (Q*L^2) ∧
          volume (relativePlanarEndpoints a (bufferedBandComponent E W0 z ∪ S))≠⊤ ∧
          volume.real (relativePlanarEndpoints a (bufferedBandComponent E W0 z ∪ S))≤Q*L^2

theorem OriginalBorelStripFamily.ComponentStripAt.rounded_of_comparisons
    {ρ : Type} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    {D : JointComponentPartition (planarBoundedBandFamily G)} {i : Fin D.count}
    {B : OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ)}
    {H K N : ℕ} {C A Q : ℝ} {p : originalJointPositiveWidthDomain ρ}
    (h : B.ComponentStripAt D i H K N C p) (hH : 2≤H) (hK : 0<K) (hC : 1≤C)
    (hA : 1≤A)
    (hcompL : roundedDyadicScale (originalJointComponentScale D i p.val)≤A*originalJointComponentScale D i p.val)
    (hcompW : roundedDyadicScale (p.val (Sum.inr ()))≤A*p.val (Sum.inr ()))
    (hprepQ : C*A^N≤Q) (hareaQ : 8*(H : ℝ)*(K : ℝ)*A^2≤Q) (hpiQ : 4*Real.pi≤Q) :
    B.RoundedComponentAt D i N Q p := by
  let L0 := originalJointComponentScale D i p.val
  let W0 := p.val (Sum.inr ())
  let L := roundedDyadicScale L0
  let W := roundedDyadicScale W0
  have hW0 : 0<W0 := p.property
  have hL0 : 0<L0 := originalJointComponentScale_pos D i p.val hW0
  have hL0L : L0≤L := le_roundedDyadicScale _
  have hL : 0<L := roundedDyadicScale_pos _
  have hW : 0<W := roundedDyadicScale_pos _
  have hA0 : 0<A := zero_lt_one.trans_le hA
  have hHr : (2 : ℝ)≤H := by exact_mod_cast hH
  have hKr : (1 : ℝ)≤K := by exact_mod_cast hK
  have hHK : (2 : ℝ)≤(H : ℝ)*(K : ℝ) := by nlinarith
  have hD : 0<4*(H : ℝ)*(K : ℝ) := by positivity
  have hD8 : 0<8*(H : ℝ)*(K : ℝ) := by positivity
  have hAA : A≤A^2 := by nlinarith
  have hlenQ : 4*(H : ℝ)*(K : ℝ)*A≤Q := by
    apply le_trans _ hareaQ
    calc
      _ ≤ (8*(H : ℝ)*(K : ℝ))*A := by gcongr <;> norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hAA hD8.le
  have hwidthQ : 4*A≤Q := by
    apply le_trans _ hareaQ
    calc
      _ ≤ (8*(H : ℝ)*(K : ℝ))*A := mul_le_mul_of_nonneg_right (by nlinarith) hA0.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hAA hD8.le
  rcases h with ⟨ha,hprep,hlenlow,hlenhi,hgeom⟩
  refine ⟨(prepared_arc_scale_constant_ge_one hC hA N).trans hprepQ,
    one_le_roundedDyadicScale _,roundedDyadicScale_mono (le_max_left _ _),
    (hprep.rescale (zero_le_one.trans hC) hA hL0 hL0L hcompL).mono_constant hL hprepQ,
    original_scaled_length_lower hD hA0 hL0.le hL.le hcompL hlenQ hlenlow,
    hlenhi.trans hL0L,?_,?_,?_⟩
  · exact original_scaled_length_lower (by norm_num : (0 : ℝ)<4) hA0 hW0.le hW.le hcompW hwidthQ le_rfl
  · exact (show W0/4≤W0 by linarith).trans (le_roundedDyadicScale _)
  · intro E hT ho hb hE hbox
    rcases hgeom E hT ho hb hE hbox with ⟨hsub,hm,harea,hlower,hcontrol⟩
    let z := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (B.anchor p)
    have hscale := originalJointComponentScale_eq D (fun r => p.val (Sum.inl (Sum.inl r)))
      hT hW0 ho hE hbox i z (by
        rw [originalComponentParameters_eta]
        simpa only [z,Equiv.apply_symm_apply] using ha)
    rw [originalComponentParameters_eta] at hscale
    change L0=bufferedComponentScale E W0 z at hscale
    change BufferedBandEndpointControl E W0 z (B.strip p W0) at hcontrol
    refine ⟨hsub,hm,harea,original_scaled_area_lower hD8 hA0 hL0.le hW0.le hL.le hW.le
      hcompL hcompW hareaQ hlower,?_⟩
    intro a ha
    rcases hcontrol a ha with ⟨hball,houter,hfinite,hreal⟩
    rw [← hscale] at hball houter hreal
    have hbound : 4*Real.pi*L0^2≤Q*L^2 :=
      mul_le_mul hpiQ (pow_le_pow_left₀ hL0.le hL0L 2) (sq_nonneg L0)
        ((by positivity : (0 : ℝ)≤4*Real.pi).trans hpiQ)
    exact ⟨hball.trans (closedBall_subset_closedBall (by linarith)),
      houter.trans (ENNReal.ofReal_le_ofReal hbound),hfinite,hreal.trans hbound⟩

theorem original_uniform_strip_rounding_powers
    (H K N minPower : ℕ) (C c : ℝ) (hH : 2≤H) (hK : 0<K) (hC : 1≤C) :
    ∃ a m : ℕ, minPower≤m ∧ 0<m ∧ ∀ P : ℝ, 2≤P →
      C*(P^a)^N≤P^m ∧ 8*(H : ℝ)*(K : ℝ)*(P^a)^2≤P^m ∧ 4*Real.pi≤P^m ∧
      ∀ W0 L0 : ℝ, P^(-c)/2≤W0 → W0≤L0 →
        roundedDyadicScale W0≤P^a*W0 ∧ roundedDyadicScale L0≤P^a*L0 := by
  obtain ⟨a,ha⟩ := original_uniform_real_rounded_scales c
  obtain ⟨n,hn⟩ := uniform_constant_le_power (C+8*(H : ℝ)*(K : ℝ)+4*Real.pi+1)
  let m := n+(N+2)*a+minPower+1
  refine ⟨a,m,by dsimp [m]; omega,by dsimp [m]; omega,?_⟩
  intro P hP
  have hP1 : 1≤P := by linarith
  have hP0 : 0≤P := by linarith
  have hHr : (2 : ℝ)≤H := by exact_mod_cast hH
  have hKr : (1 : ℝ)≤K := by exact_mod_cast hK
  have hD : 0≤8*(H : ℝ)*(K : ℝ) := by positivity
  have hCn : C≤P^n := (by linarith [Real.pi_pos] : C≤C+8*(H : ℝ)*(K : ℝ)+4*Real.pi+1).trans (hn P hP)
  have hDn : 8*(H : ℝ)*(K : ℝ)≤P^n := (by linarith [Real.pi_pos] :
    8*(H : ℝ)*(K : ℝ)≤C+8*(H : ℝ)*(K : ℝ)+4*Real.pi+1).trans (hn P hP)
  have hpin : 4*Real.pi≤P^n := (by linarith :
    4*Real.pi≤C+8*(H : ℝ)*(K : ℝ)+4*Real.pi+1).trans (hn P hP)
  have he1 : n+a*N≤m := by dsimp [m]; nlinarith
  have he2 : n+a*2≤m := by dsimp [m]; nlinarith
  have he0 : n≤m := by dsimp [m]; omega
  refine ⟨?_,?_,hpin.trans (pow_le_pow_right₀ hP1 he0),ha P hP⟩
  · calc
      C*(P^a)^N≤P^n*(P^a)^N := mul_le_mul_of_nonneg_right hCn (by positivity)
      _ = P^(n+a*N) := by rw [pow_add,pow_mul]
      _ ≤ P^m := pow_le_pow_right₀ hP1 he1
  · calc
      8*(H : ℝ)*(K : ℝ)*(P^a)^2≤P^n*(P^a)^2 := mul_le_mul_of_nonneg_right hDn (by positivity)
      _ = P^(n+a*2) := by rw [pow_add,pow_mul]
      _ ≤ P^m := pow_le_pow_right₀ hP1 he2

end PaperI
