import PaperILean.CylindricalRationalGraphs
import PaperILean.CylindricalTowerPaths
import PaperILean.JointChartSectionPaths

/-! Joint definability of the actual recursive endpoint interpolation. The
endpoints and time are arbitrary definable functions of a common parameter.
This proves the graph, rather than inferring it from pointwise semialgebraicity. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem CylindricalLift.interpolate_graph_definable
    {ρ α : Type} [Finite ρ] [Finite α] {D : Set (ρ → ℝ)} {S : Set (α → ℝ)}
    (c : CylindricalLift S) {a b : (ρ → ℝ) → (α ⊕ Unit) → ℝ}
    {x : (ρ → ℝ) → α → ℝ} {t : (ρ → ℝ) → ℝ}
    (hA : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D a))
    (hB : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D b))
    (hX : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D x))
    (hT : CADScalarDefinable D t) (ha : MapsTo a D c.region)
    (hb : MapsTo b D c.region) (hx : MapsTo x D S) :
    CADScalarDefinable D (fun p => c.interpolate (a p) (b p) (x p) (t p)) := by
  have hAx := cad_selectedGraph_coordinates hA (Sum.inl : α → α ⊕ Unit)
  have hBx := cad_selectedGraph_coordinates hB (Sum.inl : α → α ⊕ Unit)
  have hAy : CADScalarDefinable D (fun p => a p (Sum.inr ())) :=
    cad_selectedGraph_coordinates hA (fun _ : Unit => Sum.inr ())
  have hBy : CADScalarDefinable D (fun p => b p (Sum.inr ())) :=
    cad_selectedGraph_coordinates hB (fun _ : Unit => Sum.inr ())
  have hboundary (f : CylindricalBoundary S) {v : (ρ → ℝ) → α → ℝ}
      (hv : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D v))
      (hmap : MapsTo v D S) : CADScalarDefinable D (fun p => f.value (v p)) :=
    cad_selectedGraph_comp hv f.graph_definable hmap
  have hma : MapsTo (fun p => a p ∘ Sum.inl) D S := fun _ hp => (ha hp).1
  have hmb : MapsTo (fun p => b p ∘ Sum.inl) D S := fun _ hp => (hb hp).1
  cases c with
  | graph f => exact hboundary f hX hx
  | between l u _ =>
    exact (hboundary l hX hx).add (((hboundary u hX hx).sub (hboundary l hX hx)).mul
      (hT.mix
        ((hAy.sub (hboundary l hAx hma)).div ((hboundary u hAx hma).sub (hboundary l hAx hma)))
        ((hBy.sub (hboundary l hBx hmb)).div ((hboundary u hBx hmb).sub (hboundary l hBx hmb)))))
  | above l =>
    exact (hboundary l hX hx).add
      (hT.mix (hAy.sub (hboundary l hAx hma)) (hBy.sub (hboundary l hBx hmb)))
  | below u =>
    exact (hboundary u hX hx).sub
      (hT.mix ((hboundary u hAx hma).sub hAy) ((hboundary u hBx hmb).sub hBy))
  | whole => exact hT.mix hAy hBy

theorem CylindricalTower.endpointPath_selectedGraph
    {ρ α : Type} [Finite ρ] [Finite α] {D : Set (ρ → ℝ)} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S)
    {a b : (ρ → ℝ) → CADVariables α n → ℝ} {t : (ρ → ℝ) → ℝ}
    (hA : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D a))
    (hB : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D b))
    (hT : CADScalarDefinable D t) (ha : MapsTo a D S) (hb : MapsTo b D S)
    (ht : MapsTo t D (Icc (0 : ℝ) 1)) :
    (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph D (fun p => c.endpointPath (a p) (b p) (t p))) := by
  induction c with
  | base => exact hA
  | step previous lift _ ih =>
    have hAx := cad_selectedGraph_coordinates hA Sum.inl
    have hBx := cad_selectedGraph_coordinates hB Sum.inl
    have hma : MapsTo (fun p => a p ∘ Sum.inl) D _ := fun _ hp => (ha hp).1
    have hmb : MapsTo (fun p => b p ∘ Sum.inl) D _ := fun _ hp => (hb hp).1
    have hX := ih hAx hBx hma hmb
    have hm : MapsTo (fun p => previous.endpointPath (a p ∘ Sum.inl) (b p ∘ Sum.inl) (t p)) D _ :=
      fun _ hp => previous.endpointPath_mem (hma hp) (hmb hp) (ht hp)
    exact cad_selectedGraph_pair hX (lift.interpolate_graph_definable hA hB hX hT ha hb hm)

def cadPathParameterDomain {ρ : Type} (P : Set (ρ → ℝ)) : Set ((ρ ⊕ Unit) → ℝ) :=
  {v | v ∘ Sum.inl ∈ P ∧ v (Sum.inr ()) ∈ Icc (0 : ℝ) 1}

theorem cadPathParameterDomain_definable {ρ : Type} [Finite ρ]
    {P : Set (ρ → ℝ)} (hP : (univ : Set ℝ).Definable Language.ring P) :
    (univ : Set ℝ).Definable Language.ring (cadPathParameterDomain P) := by
  have h0 := realPolynomial_nonneg_definable (MvPolynomial.X (Sum.inr ()) : MvPolynomial (ρ ⊕ Unit) ℝ)
  have h1 := realPolynomial_nonneg_definable (1-MvPolynomial.X (Sum.inr ()) : MvPolynomial (ρ ⊕ Unit) ℝ)
  convert (hP.preimage_comp Sum.inl).inter (h0.inter h1) using 1
  ext v
  simp only [cadPathParameterDomain,mem_setOf_eq,mem_inter_iff,mem_preimage,
    mem_Icc,MvPolynomial.eval_X,map_sub,map_one,sub_nonneg]

theorem CylindricalTower.endpointPath_jointGraph_definable
    {ρ α : Type} [Finite ρ] [Finite α] {P : Set (ρ → ℝ)} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S)
    {a b : (ρ → ℝ) → CADVariables α n → ℝ}
    (hA : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P a))
    (hB : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P b))
    (ha : MapsTo a P S) (hb : MapsTo b P S) :
    (univ : Set ℝ).Definable Language.ring
      (jointUnitPathGraph P (fun p => c.endpointPath (a p) (b p))) := by
  let D := cadPathParameterDomain P
  have hP := selectedFunctionGraph_domain_definable P a hA
  have hD := cadPathParameterDomain_definable hP
  letI : Fintype ρ := Fintype.ofFinite ρ
  have hproj := coordinateSectionGraph_definable hD (Sum.inl : ρ → ρ ⊕ Unit)
  have hmap : MapsTo (fun v : (ρ ⊕ Unit) → ℝ => v ∘ Sum.inl) D P := fun _ hv => hv.1
  have hA' := cad_selectedGraph_comp hproj hA hmap
  have hB' := cad_selectedGraph_comp hproj hB hmap
  have hT : CADScalarDefinable D (fun v => v (Sum.inr ())) :=
    coordinateSectionGraph_definable hD (fun _ : Unit => Sum.inr ())
  have h := c.endpointPath_selectedGraph hA' hB' hT
    (fun _ hv => ha hv.1) (fun _ hv => hb hv.1) (fun _ hv => hv.2)
  let e : (ρ ⊕ Unit) ⊕ CADVariables α n → ρ ⊕ (Unit ⊕ CADVariables α n) :=
    Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)
  convert h.preimage_comp e using 1
  ext z
  change (z ∘ Sum.inl ∈ P ∧ _ ∈ unitPathGraph _) ↔ _
  simp only [selectedFunctionGraph,cadPathParameterDomain,D,jointUnitPathGraph,unitPathGraph,
    mem_setOf_eq,mem_preimage,Function.comp_def,e,Sum.elim_inl,Sum.elim_inr,funext_iff]
  constructor
  · rintro ⟨hp,ht,he⟩
    exact ⟨⟨hp,ht⟩,fun i => (he i).symm⟩
  · rintro ⟨⟨hp,ht⟩,he⟩
    exact ⟨hp,ht,fun i => (he i).symm⟩

end PaperI
