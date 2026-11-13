import PaperILean.OriginalActualPreparedComponent
import PaperILean.PreparedArcScaleComparison

/-! I1263: convert the SAME prepared centerline to physical L0. Both sides
of the original span comparison are proved, including the n=0 requirement.
Centering occurs only in the scalar estimate and never moves the strip. -/
noncomputable section
namespace PaperI
open Set

theorem OriginalJointPreparedArcData.physical_derivatives_at
    {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℝ → Fin 2 → ℝ}
    {H : ℕ} {n : Ω → ℕ} {t : Ω → ℕ → ℝ} {L : Ω → ℝ}
    {N K : ℕ} {C : ℝ} (A : OriginalJointPreparedArcData g H n t L N C K)
    (ω : Ω) (hH : 1≤H) (hC : 1≤C) (hL : 0<L ω)
    (hpart : OriginalPlanarReadoutPartition (g ω) H (n ω) (t ω))
    (hc : ContinuousOn (g ω) (Icc (0:ℝ) 1))
    (S : Set (Fin 2 → ℝ))
    (hS : Bornology.IsBounded ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' S))
    (himage : ∀ r∈Icc (0:ℝ) 1, g ω r∈S)
    (hdiam : Metric.diam ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' S)≤L ω) :
    let d := A.direction (ω,A.index ω)
    let f := fun x => A.graph ((ω,A.index ω),x)
    let a := planarDirectionSign d*g ω (t ω (A.index ω)) (planarDirectionI d)
    A.right ω-A.left ω≤L ω ∧
      (∀ x∈Icc (A.left ω) (A.right ω), ∀ j≤N,
        |iteratedDeriv j (fun q => f q-f a) x|≤(C*(4*(H : ℝ))^N)*L ω/(L ω)^j) ∧
      (∀ x∈Icc (A.left ω) (A.right ω), ∀ j, 0<j → j≤N →
        |iteratedDeriv j f x|≤(C*(4*(H : ℝ))^N)*L ω/(L ω)^j) := by
  let d := A.direction (ω,A.index ω)
  let a := planarDirectionSign d*g ω (t ω (A.index ω)) (planarDirectionI d)
  let b := planarDirectionSign d*g ω (t ω (A.index ω+1)) (planarDirectionI d)
  have hall := hpart.all_intervals hc (A.index ω)
  have hupper : b-a≤L ω :=
    (signed_coordinate_span_le_euclidean_diameter S hS (planarDirectionI d)
      (planarDirection_sign d) _ (himage _ hall.1) _ (himage _ hall.2.1)).trans hdiam
  have hHr : (1 : ℝ)≤H := by exact_mod_cast hH
  have hden : 0<4*(H : ℝ) := by positivity
  have hspan : L ω/(4*(H : ℝ))≤b-a := A.span ω
  have hell : 0<b-a := (div_pos hL hden).trans_le hspan
  have hspan' : L ω≤(4*(H : ℝ))*(b-a) := by
    have := (div_le_iff₀ hden).mp hspan
    nlinarith
  have hcompare (j : ℕ) (hj : j≤N) := prepared_arc_derivative_scale_comparison
    (zero_le_one.trans hC) (show (1 : ℝ)≤4*(H : ℝ) by linarith)
    hell hupper hspan' hj
  have hp := A.prepared ω
  have hl := hp.2.1 (show A.left ω∈Icc (A.left ω) (A.right ω) from ⟨le_rfl,hp.1.le⟩)
  have hr := hp.2.1 (show A.right ω∈Icc (A.left ω) (A.right ω) from ⟨hp.1.le,le_rfl⟩)
  change A.left ω∈Icc a b at hl
  change A.right ω∈Icc a b at hr
  refine ⟨(show A.right ω-A.left ω≤b-a by linarith [hl.1,hr.2]).trans hupper,?_,?_⟩
  · intro x hx j hj
    exact (hp.2.2.2.2.1 x hx j hj).trans (hcompare j hj)
  · intro x hx j hj hjN
    exact (hp.2.2.2.2.2 x hx j hj hjN).trans (hcompare j hjN)

theorem OriginalPreparedJointPathFamily.component_physical_derivatives
    {ρ : Type} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    {s d H N K : ℕ} {C : ℝ}
    (F : OriginalPreparedJointPathFamily.{0} univ (D.part i) s d H N C K)
    (hH : 1≤H) (hC : 1≤C)
    (a b : originalJointLargeComponentDomain D i → Fin 2 → ℝ)
    (ha : ∀ p, a p∈projectionFiber (D.part i) p.val)
    (hb : ∀ p, b p∈projectionFiber (D.part i) p.val)
    (A : OriginalJointPreparedArcData
      (fun p => F.path (Sum.elim (Sum.elim p.val (a p)) (b p))) H
      (fun p => F.activeCount (Sum.elim (Sum.elim p.val (a p)) (b p)))
      (fun p => F.cuts (Sum.elim (Sum.elim p.val (a p)) (b p)))
      (fun p => originalJointComponentScale D i p.val) N C K)
    (p : originalJointLargeComponentDomain D i) :
    let q := Sum.elim (Sum.elim p.val (a p)) (b p)
    let dir := A.direction (p,A.index p)
    let f := fun x => A.graph ((p,A.index p),x)
    let ref := planarDirectionSign dir*F.path q (F.cuts q (A.index p)) (planarDirectionI dir)
    let L := originalJointComponentScale D i p.val
    A.right p-A.left p≤L ∧
      (∀ x∈Icc (A.left p) (A.right p), ∀ j≤N,
        |iteratedDeriv j (fun z => f z-f ref) x|≤(C*(4*(H : ℝ))^N)*L/L^j) ∧
      (∀ x∈Icc (A.left p) (A.right p), ∀ j, 0<j → j≤N →
        |iteratedDeriv j f x|≤(C*(4*(H : ℝ))^N)*L/L^j) := by
  obtain ⟨γ,hγ,_⟩ := F.paths p.val (mem_univ _) (a p) (ha p) (b p) (hb p)
  apply A.physical_derivatives_at p hH hC
    (originalJointComponentScale_pos D i p.val p.property.1)
    (F.partition _ ⟨mem_univ _,ha p,hb p⟩)
    (by rw [← hγ]; exact γ.continuousOn)
    (projectionFiber (D.part i) p.val) (originalJointBand_part_euclidean_isBounded D p.val i)
  · intro r hr
    rw [← hγ]
    exact γ.mapsTo hr
  · exact le_max_right _ _

end PaperI
