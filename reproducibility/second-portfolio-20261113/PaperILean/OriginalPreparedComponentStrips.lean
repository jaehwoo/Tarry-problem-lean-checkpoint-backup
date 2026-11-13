import PaperILean.OriginalPreparedPathUniformity
import PaperILean.OriginalJointPreparedStripArea
import PaperILean.OriginalJointEndpointSelection
import PaperILean.BufferedBandEndpointLocalization

/-! Apply the uniformly prepared ORIGINAL cut paths to the actual common
large-component endpoint choice. No original label enters the construction. -/
noncomputable section
universe u
namespace PaperI
open Set MeasureTheory

theorem OriginalPreparedJointPathFamily.prepare_for_endpoints
    {ρ : Type} {P : Set (ρ → ℝ)} {S : Set ((ρ ⊕ Fin 2) → ℝ)}
    {s d H N K : ℕ} {C : ℝ}
    (F : OriginalPreparedJointPathFamily.{u} P S s d H N C K)
    {Ω : Type u} [MeasurableSpace Ω] (p : Ω → P) (a b : Ω → Fin 2 → ℝ)
    (hp : Measurable p) (ha : Measurable a) (hb : Measurable b)
    (haS : ∀ ω, a ω∈projectionFiber S (p ω).val)
    (hbS : ∀ ω, b ω∈projectionFiber S (p ω).val)
    (L : Ω → ℝ) (hL : ∀ ω, 0<L ω)
    (hsep : ∀ ω, L ω/2 ≤ dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (a ω))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (b ω))) :
    Nonempty (OriginalJointPreparedArcData
      (fun ω => F.path (Sum.elim (Sum.elim (p ω).val (a ω)) (b ω))) H
      (fun ω => F.activeCount (Sum.elim (Sum.elim (p ω).val (a ω)) (b ω)))
      (fun ω => F.cuts (Sum.elim (Sum.elim (p ω).val (a ω)) (b ω))) L N C K) := by
  let q : Ω → cellChainEndpointDomain P S := fun ω =>
    ⟨Sum.elim (Sum.elim (p ω).val (a ω)) (b ω),(p ω).property,haS ω,hbS ω⟩
  have hq : Measurable q := by
    apply Measurable.subtype_mk
    apply measurable_pi_lambda
    intro i
    rcases i with (r | k) | k
    · exact (measurable_pi_apply r).comp (measurable_subtype_coe.comp hp)
    · exact (measurable_pi_apply k).comp ha
    · exact (measurable_pi_apply k).comp hb
  apply F.prepare Ω q hq L hL
  intro ω
  obtain ⟨γ,hγ,_⟩ := F.paths (p ω).val (p ω).property (a ω) (haS ω) (b ω) (hbS ω)
  have hzero : F.path (q ω).val 0=a ω := by rw [← hγ]; exact γ.source
  have hone : F.path (q ω).val 1=b ω := by rw [← hγ]; exact γ.target
  simpa only [hzero,hone] using hsep ω

theorem OriginalPreparedJointPathFamily.large_component_data
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity) (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    {s d H N K : ℕ} {C : ℝ}
    (F : OriginalPreparedJointPathFamily.{0} univ (D.part i) s d H N C K) :
    ∃ a b : originalJointLargeComponentDomain D i → Fin 2 → ℝ,
      Measurable a ∧ Measurable b ∧
      (∀ p, a p∈projectionFiber (D.part i) p.val ∧
        b p∈projectionFiber (D.part i) p.val ∧ a p≠b p ∧
        originalJointComponentScale D i p.val/2 <
          dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (a p))
            ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (b p)) ∧
        dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (a p))
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (b p)) ≤ originalJointComponentScale D i p.val) ∧
      Nonempty (OriginalJointPreparedArcData
        (fun p => F.path (Sum.elim (Sum.elim p.val (a p)) (b p))) H
        (fun p => F.activeCount (Sum.elim (Sum.elim p.val (a p)) (b p)))
        (fun p => F.cuts (Sum.elim (Sum.elim p.val (a p)) (b p)))
        (fun p => originalJointComponentScale D i p.val) N C K) := by
  obtain ⟨a,b,ha,hb,_,hend⟩ := published_originalJointLargeEndpoints hCAD hQE hHardt D i
  let p0 : originalJointLargeComponentDomain D i →
      (univ : Set ((((ρ ⊕ Unit) ⊕ Unit) → ℝ))) := fun p => ⟨p.val,mem_univ _⟩
  have hp0 : Measurable p0 := measurable_subtype_coe.subtype_mk
  refine ⟨a,b,ha,hb,hend,?_⟩
  exact F.prepare_for_endpoints p0 a b hp0 ha hb
    (fun p => (hend p).1) (fun p => (hend p).2.1)
    (fun p => originalJointComponentScale D i p.val)
    (fun p => originalJointComponentScale_pos D i p.val p.property.1)
    (fun p => (hend p).2.2.2.1.le)

theorem OriginalJointPreparedArcData.endpoint_control_at
    {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℝ → Fin 2 → ℝ}
    {H : ℕ} {n : Ω → ℕ} {t : Ω → ℕ → ℝ} {L : Ω → ℝ}
    {N K : ℕ} {C : ℝ} (A : OriginalJointPreparedArcData g H n t L N C K) (ω : Ω)
    (hpart : OriginalPlanarReadoutPartition (g ω) H (n ω) (t ω))
    (hc : ContinuousOn (g ω) (Icc (0:ℝ) 1))
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (W : ℝ) (z : WithLp 2 (Fin 2 → ℝ))
    (hE : Bornology.IsBounded E) (hW : 0≤W)
    (himage : ∀ r, r∈Icc (0:ℝ) 1 →
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm (g ω r)∈bufferedBandComponent E W z) :
    BufferedBandEndpointControl E W z
      (signedPlanarStrip (planarDirectionI (A.direction (ω,A.index ω)))
        (planarDirectionSign (A.direction (ω,A.index ω)))
        (fun x => A.graph ((ω,A.index ω),x)) (Icc (A.left ω) (A.right ω)) (W/4)) := by
  have hall := hpart.all_intervals hc (A.index ω)
  have hArc := A.arcs ω (A.index ω)
  apply bufferedBand_signed_strip_endpoint_control hE hW
  intro q hq
  obtain ⟨r,hr,hpoint⟩ := signedPlanarStripPoint_zero_eq_path
    (g ω) (t ω (A.index ω)) (t ω (A.index ω+1)) _ _
    (planarDirection_distinct _) _ (planarDirection_sign _)
    (fun x => A.graph ((ω,A.index ω),x)) hArc.2.2.2.1
    (fun q hq => by
      obtain ⟨r,hr,he,_⟩ := hArc.2.2.2.2 q hq
      exact ⟨r,hr,he.symm⟩) ((A.prepared ω).2.1 hq)
  rw [hpoint]
  exact himage r ⟨hall.1.1.trans hr.1,hr.2.trans hall.2.1.2⟩

end PaperI
