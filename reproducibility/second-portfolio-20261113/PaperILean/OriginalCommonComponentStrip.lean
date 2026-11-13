import PaperILean.OriginalStripFamilyBranches

/-! I1263/I1265: choose ONE common strip per positive-width component entry,
before any original label. Empty entries are totalized but geometry is claimed
only for nonempty fibres. The equality case uses the original small branch. -/
noncomputable section
namespace PaperI
open Set MeasureTheory

def originalJointPositiveWidthDomain (ρ : Type*) : Set (((ρ ⊕ Unit) ⊕ Unit) → ℝ) :=
  {p | 0<p (Sum.inr ())}

def OriginalBorelStripFamily.ComponentStripAt
    {ρ : Type} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (B : OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ))
    (H K N : ℕ) (C : ℝ) (p : originalJointPositiveWidthDomain ρ) : Prop :=
  let L := originalJointComponentScale D i p.val
  let W := p.val (Sum.inr ())
  B.anchor p∈projectionFiber (D.part i) p.val ∧
    B.PhysicalPreparedAt N C L p ∧
    L/(4*(H : ℝ)*(K : ℝ))≤B.right p-B.left p ∧ B.right p-B.left p≤L ∧
    ∀ E : Set (WithLp 2 (Fin 2 → ℝ)),
      0≤p.val (Sum.inl (Sum.inr ())) → IsOpen E → Bornology.IsBounded E →
      (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=projectionFiber G (fun r => p.val (Sum.inl (Sum.inl r))) →
      (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox (p.val (Sum.inl (Sum.inr ()))) →
      B.strip p W⊆E ∧ MeasurableSet (B.strip p W) ∧
        volume.real (B.strip p W)=(B.right p-B.left p)*W/2 ∧
        L*W/(8*(H : ℝ)*(K : ℝ))≤volume.real (B.strip p W) ∧
        BufferedBandEndpointControl E W ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (B.anchor p)) (B.strip p W)

theorem OriginalPreparedJointPathFamily.common_component_strip
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity) (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    {s d H N K : ℕ} {C : ℝ}
    (F : OriginalPreparedJointPathFamily.{0} univ (D.part i) s d H N C K)
    (hH : 2≤H) (hC : 1≤C) (hK : 0<K) :
    ∃ B : OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ),
      ∀ p, (projectionFiber (D.part i) p.val).Nonempty →
        B.ComponentStripAt D i H K N (C*(4*(H : ℝ))^N) p := by
  classical
  obtain ⟨a,b,ha,hb,hend,A,hgeom⟩ := F.large_component_strips hCAD hQE hHardt D i
  obtain ⟨BL,hBL⟩ := F.component_borel_strip_family hQE hHardt D i (by omega) hC a b ha hb
    (fun p => (hend p).1) (fun p => (hend p).2.1) A
  obtain ⟨x,hx,_,hxS⟩ := published_original_joint_component_center hCAD hQE hHardt D i
  let large : Set (originalJointPositiveWidthDomain ρ) :=
    {p | p.val∈originalJointLargeComponentDomain D i}
  have hlarge : MeasurableSet large :=
    (published_originalJointLargeComponentDomain_measurable hQE D i).preimage measurable_subtype_coe
  let ql : large → originalJointLargeComponentDomain D i := fun p => ⟨p.val.val,p.property⟩
  have hql : Measurable ql := (measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk
  let qs : (largeᶜ : Set (originalJointPositiveWidthDomain ρ)) → (((ρ ⊕ Unit) ⊕ Unit) → ℝ) :=
    fun p => p.val.val
  have hqs : Measurable qs := measurable_subtype_coe.comp measurable_subtype_coe
  let SB := originalBorelRectangle (x ∘ qs) (hx.comp hqs)
    (fun p => p.val.val (Sum.inr ())) ((measurable_pi_apply _).comp hqs)
  let LB := BL.comp ql hql
  let B := LB.glue large hlarge SB
  refine ⟨B,?_⟩
  intro p hne
  have hW : 0<p.val (Sum.inr ()) := p.property
  have hHr : (2 : ℝ)≤H := by exact_mod_cast hH
  have hKr : (1 : ℝ)≤K := by exact_mod_cast hK
  have hCp : 1≤C*(4*(H : ℝ))^N :=
    prepared_arc_scale_constant_ge_one hC (by linarith) N
  by_cases hp : p∈large
  · let lp : originalJointLargeComponentDomain D i := ql ⟨p,hp⟩
    rcases hBL lp with ⟨haeq,hstrip,hleneq,hprep,hlo,hhi⟩
    have hbanchor : B.anchor p=a lp := by simpa [B,OriginalBorelStripFamily.glue,LB,
      OriginalBorelStripFamily.comp,hp] using haeq
    have hbstrip (W : ℝ) : B.strip p W=A.strip lp W := by
      rw [OriginalBorelStripFamily.strip_glue_of_mem large hlarge LB SB p hp]
      exact hstrip W
    have hblen : B.right p-B.left p=A.right lp-A.left lp := by
      simpa [B,OriginalBorelStripFamily.glue,LB,OriginalBorelStripFamily.comp,hp] using hleneq
    have hbprep : B.PhysicalPreparedAt N (C*(4*(H : ℝ))^N)
        (originalJointComponentScale D i p.val) p := by
      simpa [B,OriginalBorelStripFamily.PhysicalPreparedAt,OriginalBorelStripFamily.glue,
        LB,OriginalBorelStripFamily.comp,hp,lp] using hprep
    refine ⟨by rw [hbanchor]; exact (hend lp).1,hbprep,?_,?_,?_⟩
    · simpa [B,OriginalBorelStripFamily.glue,LB,OriginalBorelStripFamily.comp,hp,lp] using hlo
    · simpa [B,OriginalBorelStripFamily.glue,LB,OriginalBorelStripFamily.comp,hp,lp] using hhi
    · intro E hT ho hbounded hE hbox
      rcases hgeom lp E hT ho hbounded hE hbox with ⟨hsub,hm,harea,hlower,hcontrol⟩
      rw [hbstrip,hbanchor]
      exact ⟨hsub,hm,by rw [hblen]; exact harea,hlower,hcontrol⟩
  · let sp : (largeᶜ : Set (originalJointPositiveWidthDomain ρ)) := ⟨p,hp⟩
    have hsmall : planarFiberDiameter (D.part i) p.val≤p.val (Sum.inr ()) := by
      by_contra h
      exact hp ⟨p.property,lt_of_not_ge h⟩
    have hscale : originalJointComponentScale D i p.val=p.val (Sum.inr ()) := max_eq_left hsmall
    have hbanchor : B.anchor p=x p.val := by
      simp [B,OriginalBorelStripFamily.glue,SB,originalBorelRectangle,qs,hp]
    have hbstrip : B.strip p (p.val (Sum.inr ()))=
        bufferedPointRectangle ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (x p.val)) (p.val (Sum.inr ())) := by
      rw [OriginalBorelStripFamily.strip_glue_of_not_mem large hlarge LB SB p hp]
      exact originalBorelRectangle_strip _ _ _ _ sp
    have hblen : B.right p-B.left p=p.val (Sum.inr ())/2 := by
      simpa [B,OriginalBorelStripFamily.glue,SB,originalBorelRectangle,qs,hp] using
        (show (x p.val 0+p.val (Sum.inr ())/4)-(x p.val 0-p.val (Sum.inr ())/4)=
          p.val (Sum.inr ())/2 by ring)
    have hbprep : B.PhysicalPreparedAt N (C*(4*(H : ℝ))^N)
        (originalJointComponentScale D i p.val) p := by
      have hprep := originalBorelRectangle_physical (x ∘ qs) (hx.comp hqs)
        (fun p => p.val.val (Sum.inr ())) ((measurable_pi_apply _).comp hqs)
        sp p.property N (zero_le_one.trans hCp)
      rw [hscale]
      simpa [B,OriginalBorelStripFamily.PhysicalPreparedAt,OriginalBorelStripFamily.glue,
        SB,qs,hp,sp] using hprep
    have hden : (2 : ℝ)≤4*(H : ℝ)*(K : ℝ) := by nlinarith
    have hlo : p.val (Sum.inr ())/(4*(H : ℝ)*(K : ℝ))≤p.val (Sum.inr ())/2 := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ)<4*(H : ℝ)*(K : ℝ))).mpr
      nlinarith [mul_le_mul_of_nonneg_left hden p.property.le]
    refine ⟨by rw [hbanchor]; exact hxS p.val hne,hbprep,?_,?_,?_⟩
    · simpa only [hscale,hblen] using hlo
    · rw [hscale,hblen]; linarith
    · intro E hT ho hbounded hE hbox
      let coeff : ρ → ℝ := fun r => p.val (Sum.inl (Sum.inl r))
      have heq : Sum.elim (Sum.elim coeff (fun _ : Unit => p.val (Sum.inl (Sum.inr ()))))
          (fun _ : Unit => p.val (Sum.inr ()))=p.val := by
        funext r
        rcases r with (r | u) | u
        · rfl
        · cases u; rfl
        · cases u; rfl
      have hg := original_joint_small_rectangle_geometry D i coeff hT p.property ho hbounded hE hbox
        (x p.val) (by rw [heq]; exact hxS p.val hne) (by rw [heq]; exact hsmall)
      simp only [heq] at hg
      rcases hg with ⟨_,hsub,hm,harea,hcontrol⟩
      rw [hbstrip,hbanchor]
      refine ⟨hsub,hm,?_,?_,hcontrol⟩
      · rw [hblen,hscale] at *
        linarith [harea]
      · have harea0 : 0≤originalJointComponentScale D i p.val*p.val (Sum.inr ()) := by
          rw [hscale]; exact mul_nonneg hW.le hW.le
        calc
          originalJointComponentScale D i p.val*p.val (Sum.inr ())/(8*(H : ℝ)*(K : ℝ))
              ≤ originalJointComponentScale D i p.val*p.val (Sum.inr ())/4 := by
                apply div_le_div_of_nonneg_left harea0 (by norm_num)
                nlinarith
          _ = _ := harea.symm

end PaperI
