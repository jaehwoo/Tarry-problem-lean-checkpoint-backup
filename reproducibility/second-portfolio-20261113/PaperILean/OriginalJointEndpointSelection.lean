import PaperILean.JointSeparatedEndpoints
import PaperILean.OriginalJointComponentScales

/-! I1263/I1265: apply the fixed joint endpoint choice to the already
constructed original bounded-search component catalogue. The large branch
retains W0>0 and W0<diam C, so L0=diam C exactly. All original labels in the
same entry use these same endpoints. No joint path or strip is claimed. -/
noncomputable section
namespace PaperI
open Set

def originalJointLargeComponentDomain {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count) :
    Set (((ρ ⊕ Unit) ⊕ Unit) → ℝ) :=
  {p | 0 < p (Sum.inr ()) ∧ p (Sum.inr ()) < planarFiberDiameter (D.part i) p}

theorem originalJointLargeComponentDomain_subset_positiveDiameter {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count) :
    originalJointLargeComponentDomain D i ⊆ planarPositiveDiameterDomain (D.part i) := by
  intro p hp
  exact hp.1.trans hp.2

theorem published_originalJointLargeComponentDomain_measurable
    (hQE : PublishedRealSemialgebraicity) {ρ : Type} [Finite ρ]
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count) :
    MeasurableSet (originalJointLargeComponentDomain D i) :=
  (measurableSet_lt measurable_const (measurable_pi_apply (Sum.inr ()))).inter
    (published_originalJointComponentBranches_measurable hQE D i).2

theorem originalJointLargeComponentDomain_nonpos_width {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    {p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ} (hp : p (Sum.inr ()) ≤ 0) :
    p ∉ originalJointLargeComponentDomain D i := by
  intro h
  exact (not_lt_of_ge hp) h.1

theorem originalJointLargeComponentDomain_empty_fiber {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    {p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ} (he : projectionFiber (D.part i) p = ∅) :
    p ∉ originalJointLargeComponentDomain D i := by
  intro hp
  have h := originalJointLargeComponentDomain_subset_positiveDiameter D i hp
  change 0 < planarFiberDiameter (D.part i) p at h
  rw [planarFiberDiameter_empty he] at h
  exact (lt_irrefl 0) h

theorem originalJointLargeComponentScale_eq_diameter {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    {p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ} (hp : p ∈ originalJointLargeComponentDomain D i) :
    originalJointComponentScale D i p = planarFiberDiameter (D.part i) p :=
  max_eq_right hp.2.le

/-- No choice depends on an original label, and no new scale constant is
introduced. The two constants are literally 1/2 and 1. -/
theorem published_originalJointLargeEndpoints
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count) :
    ∃ a b : originalJointLargeComponentDomain D i → Fin 2 → ℝ,
      Measurable a ∧ Measurable b ∧
      MeasurableSet {v : originalJointLargeComponentDomain D i ×
          ((Fin 2 → ℝ) × (Fin 2 → ℝ)) | (a v.1,b v.1) = v.2} ∧
      ∀ p, a p ∈ projectionFiber (D.part i) p.val ∧
        b p ∈ projectionFiber (D.part i) p.val ∧ a p ≠ b p ∧
        originalJointComponentScale D i p.val/2 <
          dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (a p))
            ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (b p)) ∧
        dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (a p))
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (b p)) ≤ originalJointComponentScale D i p.val := by
  obtain ⟨a,b,ha,hb,hpair⟩ := published_jointSeparatedEndpoints hCAD hQE hHardt
    (D.semialgebraic i) (fun p => originalJointBand_part_euclidean_isBounded D p i)
  let g : originalJointLargeComponentDomain D i → planarPositiveDiameterDomain (D.part i) :=
    fun p => ⟨p.val,originalJointLargeComponentDomain_subset_positiveDiameter D i p.property⟩
  have hg : Measurable g := measurable_subtype_coe.subtype_mk
  refine ⟨a ∘ g,b ∘ g,ha.comp hg,hb.comp hg,
    jointEndpointPair_graph_measurable _ _ (ha.comp hg) (hb.comp hg),?_⟩
  intro p
  rw [originalJointLargeComponentScale_eq_diameter D i p.property]
  exact hpair (g p)

theorem originalJointEndpoint_mem_actual_component {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (p : ρ → ℝ) {T W : ℝ} (hT : 0 ≤ T) (hW : 0 < W)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G p)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    (i : Fin D.count) (z : WithLp 2 (Fin 2 → ℝ))
    (hz : (WithLp.equiv 2 (Fin 2 → ℝ)) z ∈ projectionFiber (D.part i)
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)))
    {x : Fin 2 → ℝ}
    (hx : x ∈ projectionFiber (D.part i)
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W))) :
    (WithLp.equiv 2 (Fin 2 → ℝ)).symm x ∈ bufferedBandComponent E W z := by
  rw [originalJointBand_part_eq_component D p hT hW ho hE hbox i z hz] at hx
  have h : (WithLp.equiv 2 (Fin 2 → ℝ)).symm x ∈
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' bufferedBandCoordinates E W z := ⟨x,hx,rfl⟩
  rwa [bufferedBandCoordinates_euclidean_image] at h

/-- The original label predicate is unchanged. Every endpoint in the common
catalogue fiber belongs to the component of every assigned label, even for
an infinite or uncountable label type. -/
theorem originalDyadicComponentAssigned_endpoint_mem {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) {ω : Ω} {j : Λ} {k : ℤ} {i : Fin D.count}
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E) (hT : 0 ≤ radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω))
    (z : WithLp 2 (Fin 2 → ℝ))
    (hpoint : point ω j = (WithLp.equiv 2 (Fin 2 → ℝ)) z)
    (hj : originalDyadicComponentAssigned D active param radius point ω j k i)
    {x : Fin 2 → ℝ}
    (hx : x ∈ projectionFiber (D.part i)
      (Sum.elim (Sum.elim (param ω) (fun _ => radius ω)) (fun _ => (2:ℝ)^k))) :
    (WithLp.equiv 2 (Fin 2 → ℝ)).symm x ∈ bufferedBandComponent E ((2:ℝ)^k) z := by
  rw [originalDyadicComponentAssigned_actual_component D active param radius point
    ho hT hE hbox z hpoint hj] at hx
  have h : (WithLp.equiv 2 (Fin 2 → ℝ)).symm x ∈
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' bufferedBandCoordinates E ((2:ℝ)^k) z := ⟨x,hx,rfl⟩
  rwa [bufferedBandCoordinates_euclidean_image] at h

end PaperI
