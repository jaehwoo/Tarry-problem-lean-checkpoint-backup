import PaperILean.OriginalJointSmallComponentStrips

/-! Complete the original large-component geometric application: common
endpoints, the same joint path, the actual first-maximum prepared graph, its
buffer, Euclidean area and endpoint localization in the represented open set. -/
noncomputable section
namespace PaperI
open Set MeasureTheory

def OriginalJointPreparedArcData.strip
    {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℝ → Fin 2 → ℝ}
    {H : ℕ} {n : Ω → ℕ} {t : Ω → ℕ → ℝ} {L : Ω → ℝ}
    {N K : ℕ} {C : ℝ} (A : OriginalJointPreparedArcData g H n t L N C K)
    (ω : Ω) (W : ℝ) : Set (WithLp 2 (Fin 2 → ℝ)) :=
  signedPlanarStrip (planarDirectionI (A.direction (ω,A.index ω)))
    (planarDirectionSign (A.direction (ω,A.index ω)))
    (fun x => A.graph ((ω,A.index ω),x)) (Icc (A.left ω) (A.right ω)) (W/4)

theorem OriginalPreparedJointPathFamily.large_component_strips
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
      ∃ A : OriginalJointPreparedArcData
        (fun p => F.path (Sum.elim (Sum.elim p.val (a p)) (b p))) H
        (fun p => F.activeCount (Sum.elim (Sum.elim p.val (a p)) (b p)))
        (fun p => F.cuts (Sum.elim (Sum.elim p.val (a p)) (b p)))
        (fun p => originalJointComponentScale D i p.val) N C K,
      ∀ p : originalJointLargeComponentDomain D i,
      ∀ E : Set (WithLp 2 (Fin 2 → ℝ)),
      0≤p.val (Sum.inl (Sum.inr ())) → IsOpen E → Bornology.IsBounded E →
      (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=
        projectionFiber G (fun r => p.val (Sum.inl (Sum.inl r))) →
      (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox (p.val (Sum.inl (Sum.inr ()))) →
      let W := p.val (Sum.inr ())
      A.strip p W⊆E ∧ MeasurableSet (A.strip p W) ∧
        volume.real (A.strip p W)=(A.right p-A.left p)*W/2 ∧
        originalJointComponentScale D i p.val*W/(8*(H : ℝ)*(K : ℝ))≤volume.real (A.strip p W) ∧
        BufferedBandEndpointControl E W ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (a p)) (A.strip p W) := by
  obtain ⟨a,b,ha,hb,hend,⟨A⟩⟩ := F.large_component_data hCAD hQE hHardt D i
  refine ⟨a,b,ha,hb,hend,A,?_⟩
  have hpart (p : originalJointLargeComponentDomain D i) := F.partition
    (Sum.elim (Sum.elim p.val (a p)) (b p)) ⟨mem_univ _,(hend p).1,(hend p).2.1⟩
  have hc (p : originalJointLargeComponentDomain D i) :
      ContinuousOn (F.path (Sum.elim (Sum.elim p.val (a p)) (b p))) (Icc (0:ℝ) 1) := by
    obtain ⟨γ,hγ,_⟩ := F.paths p.val (mem_univ _) (a p) (hend p).1 (b p) (hend p).2.1
    rw [← hγ]
    exact γ.continuousOn
  intro p E hT ho hbounded hE hbox
  let coeff : ρ → ℝ := fun r => p.val (Sum.inl (Sum.inl r))
  let T := p.val (Sum.inl (Sum.inr ()))
  let W := p.val (Sum.inr ())
  let z := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (a p)
  have heq : Sum.elim (Sum.elim coeff (fun _ => T)) (fun _ => W)=p.val := by
    funext r
    rcases r with (r | u) | u
    · rfl
    · cases u; rfl
    · cases u; rfl
  have hza : (WithLp.equiv 2 (Fin 2 → ℝ)) z∈projectionFiber (D.part i)
      (Sum.elim (Sum.elim coeff (fun _ => T)) (fun _ => W)) := by
    change a p∈_
    rw [heq]
    exact (hend p).1
  have himage (r : ℝ) (hr : r∈Icc (0:ℝ) 1) :
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm
        (F.path (Sum.elim (Sum.elim p.val (a p)) (b p)) r)∈bufferedBandComponent E W z := by
    apply originalJointEndpoint_mem_actual_component D coeff hT p.property.1 ho hE hbox i z hza
    rw [heq]
    obtain ⟨γ,hγ,_⟩ := F.paths p.val (mem_univ _) (a p) (hend p).1 (b p) (hend p).2.1
    rw [← hγ]
    exact γ.mapsTo hr
  have hbuffer (r : ℝ) (hr : r∈Icc (0:ℝ) 1) :=
    (bufferedBandComponent_buffer (himage r hr)).1.le
  have harea := A.strip_area_at p (hpart p) (hc p) E W p.property.1 hbuffer
  have hcontrol := A.endpoint_control_at p (hpart p) (hc p) E W z hbounded p.property.1.le himage
  exact ⟨harea.1,harea.2.1,harea.2.2.1,harea.2.2.2,hcontrol⟩

end PaperI
