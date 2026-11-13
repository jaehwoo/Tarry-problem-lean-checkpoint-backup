import PaperILean.OriginalBorelStripFamily

/-! Actual Borel data for the two ORIGINAL branches. The reference value is
jointly measurable and changes only the scalar centering convention. -/
noncomputable section
namespace PaperI
open Set MeasureTheory

def OriginalBorelStripFamily.PhysicalPreparedAt {Ω : Type*} [MeasurableSpace Ω]
    (B : OriginalBorelStripFamily Ω) (N : ℕ) (C L : ℝ) (ω : Ω) : Prop :=
  B.left ω<B.right ω ∧ AnalyticOnNhd ℝ (fun x => B.graph (ω,x)) (Icc (B.left ω) (B.right ω)) ∧
    (∀ x∈Icc (B.left ω) (B.right ω), ∀ j≤N,
      |iteratedDeriv j (fun z => B.graph (ω,z)-B.graph (ω,B.reference ω)) x|≤C*L/L^j) ∧
    (∀ x∈Icc (B.left ω) (B.right ω), ∀ j, 0<j → j≤N →
      |iteratedDeriv j (fun z => B.graph (ω,z)) x|≤C*L/L^j)

def originalBorelRectangle {Ω : Type*} [MeasurableSpace Ω]
    (x : Ω → Fin 2 → ℝ) (hx : Measurable x) (W : Ω → ℝ) (hW : Measurable W) :
    OriginalBorelStripFamily Ω where
  direction := fun _ => 0
  graph := fun v => x v.1 1
  left := fun ω => x ω 0-W ω/4
  right := fun ω => x ω 0+W ω/4
  reference := fun _ => 0
  anchor := x
  measurable_direction := measurable_const
  measurable_graph := ((measurable_pi_apply 1).comp hx).comp measurable_fst
  measurable_left := ((measurable_pi_apply 0).comp hx).sub (hW.div_const 4)
  measurable_right := ((measurable_pi_apply 0).comp hx).add (hW.div_const 4)
  measurable_reference := measurable_const
  measurable_anchor := hx

theorem originalBorelRectangle_strip {Ω : Type*} [MeasurableSpace Ω]
    (x : Ω → Fin 2 → ℝ) (hx : Measurable x) (W : Ω → ℝ) (hW : Measurable W) (ω : Ω) :
    (originalBorelRectangle x hx W hW).strip ω (W ω)=
      bufferedPointRectangle ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (x ω)) (W ω) := rfl

theorem originalBorelRectangle_physical {Ω : Type*} [MeasurableSpace Ω]
    (x : Ω → Fin 2 → ℝ) (hx : Measurable x) (W : Ω → ℝ) (hW : Measurable W)
    (ω : Ω) (hpos : 0<W ω) (N : ℕ) {C : ℝ} (hC : 0≤C) :
    (originalBorelRectangle x hx W hW).PhysicalPreparedAt N C (W ω) ω := by
  have hzero := constant_centerline_all_order_prepared (x ω 1)
  refine ⟨by dsimp [originalBorelRectangle]; linarith,
    (by change AnalyticOnNhd ℝ (fun _ : ℝ => x ω 1) _; exact analyticOnNhd_const),?_,?_⟩
  · intro z hz j hj
    change |iteratedDeriv j (fun _ : ℝ => x ω 1-x ω 1) z|≤_
    rw [hzero.2.1 j z,abs_zero]
    positivity
  · intro z hz j hj hjN
    change |iteratedDeriv j (fun _ : ℝ => x ω 1) z|≤_
    rw [hzero.2.2 j hj z,abs_zero]
    positivity

theorem OriginalPreparedJointPathFamily.component_borel_strip_family
    (hQE : PublishedRealSemialgebraicity) (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    {s d H N K : ℕ} {C : ℝ}
    (F : OriginalPreparedJointPathFamily.{0} univ (D.part i) s d H N C K)
    (hH : 1≤H) (hC : 1≤C)
    (a b : originalJointLargeComponentDomain D i → Fin 2 → ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (haS : ∀ p, a p∈projectionFiber (D.part i) p.val)
    (hbS : ∀ p, b p∈projectionFiber (D.part i) p.val)
    (A : OriginalJointPreparedArcData
      (fun p => F.path (Sum.elim (Sum.elim p.val (a p)) (b p))) H
      (fun p => F.activeCount (Sum.elim (Sum.elim p.val (a p)) (b p)))
      (fun p => F.cuts (Sum.elim (Sum.elim p.val (a p)) (b p)))
      (fun p => originalJointComponentScale D i p.val) N C K) :
    ∃ B : OriginalBorelStripFamily (originalJointLargeComponentDomain D i),
      ∀ p, B.anchor p=a p ∧ (∀ W, B.strip p W=A.strip p W) ∧
        B.right p-B.left p=A.right p-A.left p ∧
        B.PhysicalPreparedAt N (C*(4*(H : ℝ))^N) (originalJointComponentScale D i p.val) p ∧
        originalJointComponentScale D i p.val/(4*(H : ℝ)*(K : ℝ))≤B.right p-B.left p ∧
        B.right p-B.left p≤originalJointComponentScale D i p.val := by
  let q : originalJointLargeComponentDomain D i → cellChainEndpointDomain univ (D.part i) :=
    fun p => ⟨Sum.elim (Sum.elim p.val (a p)) (b p),mem_univ _,haS p,hbS p⟩
  have hq : Measurable q := by
    apply Measurable.subtype_mk
    apply measurable_pi_lambda
    intro r
    rcases r with (r | j) | j
    · exact (measurable_pi_apply r).comp measurable_subtype_coe
    · exact (measurable_pi_apply j).comp ha
    · exact (measurable_pi_apply j).comp hb
  have htime (p) : F.cuts (q p).val (A.index p)∈Icc (0:ℝ) 1 := by
    obtain ⟨γ,hγ,_⟩ := F.paths p.val (mem_univ _) (a p) (haS p) (b p) (hbS p)
    exact ((F.partition (q p).val (q p).property).all_intervals
      (by rw [← hγ]; exact γ.continuousOn) (A.index p)).1
  have href := published_joint_path_signed_coordinate_measurable hQE hHardt F.joint_graph q
    (fun p => F.cuts (q p).val (A.index p))
    (fun p => A.direction (p,A.index p)) hq A.measurable_time_left
    A.measurable_selected_direction htime
  let B : OriginalBorelStripFamily (originalJointLargeComponentDomain D i) := {
    direction := fun p => A.direction (p,A.index p)
    graph := fun v => A.graph ((v.1,A.index v.1),v.2)
    left := A.left
    right := A.right
    reference := fun p => planarDirectionSign (A.direction (p,A.index p))*
      F.path (q p).val (F.cuts (q p).val (A.index p)) (planarDirectionI (A.direction (p,A.index p)))
    anchor := a
    measurable_direction := A.measurable_selected_direction
    measurable_graph := A.measurable_selected_graph
    measurable_left := A.measurable_left
    measurable_right := A.measurable_right
    measurable_reference := href
    measurable_anchor := ha }
  refine ⟨B,?_⟩
  intro p
  have hphys := F.component_physical_derivatives D i hH hC a b haS hbS A p
  exact ⟨rfl,fun _ => rfl,rfl,⟨(A.prepared p).1,(A.prepared p).2.2.2.1,hphys.2⟩,
    A.macroscopic_length p,hphys.1⟩

theorem OriginalBorelStripFamily.physical_comp {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] (B : OriginalBorelStripFamily Ω)
    (q : Ξ → Ω) (hq : Measurable q) (ξ : Ξ) (N : ℕ) (C L : ℝ) :
    (B.comp q hq).PhysicalPreparedAt N C L ξ ↔ B.PhysicalPreparedAt N C L (q ξ) := Iff.rfl

theorem OriginalBorelStripFamily.physical_glue_of_mem {Ω : Type*} [MeasurableSpace Ω]
    (s : Set Ω) (hs : MeasurableSet s) (A : OriginalBorelStripFamily s)
    (B : OriginalBorelStripFamily (sᶜ : Set Ω)) (ω : Ω) (h : ω∈s) (N : ℕ) (C L : ℝ) :
    (A.glue s hs B).PhysicalPreparedAt N C L ω ↔ A.PhysicalPreparedAt N C L ⟨ω,h⟩ := by
  classical
  simp [PhysicalPreparedAt,glue,h]

theorem OriginalBorelStripFamily.physical_glue_of_not_mem {Ω : Type*} [MeasurableSpace Ω]
    (s : Set Ω) (hs : MeasurableSet s) (A : OriginalBorelStripFamily s)
    (B : OriginalBorelStripFamily (sᶜ : Set Ω)) (ω : Ω) (h : ω∉s) (N : ℕ) (C L : ℝ) :
    (A.glue s hs B).PhysicalPreparedAt N C L ω ↔ B.PhysicalPreparedAt N C L ⟨ω,h⟩ := by
  classical
  simp [PhysicalPreparedAt,glue,h]

end PaperI
