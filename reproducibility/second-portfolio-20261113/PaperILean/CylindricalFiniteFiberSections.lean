import PaperILean.CylindricalJointConnectedPaths
import PaperILean.CylindricalJointSelector
import Mathlib.Topology.Separation.Connected

/-! Original CAD route: every retained finite-fiber leaf is the graph of its
actual continuous section. Empty fibers are allowed; no single global branch,
continuity across strata, or quantitative derivative bound is asserted. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem cadKeepCoordinate_output {ρ : Type} (n : ℕ) (i : Fin n) :
    cadKeepCoordinate (ρ := ρ) n (cadOutputCoordinate n i) = cadOutputCoordinate n i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrArg Sum.inl (ih j)

theorem finite_continuous_path_endpoints_eq {X : Type*} [TopologicalSpace X] [T1Space X]
    {S : Set X} (hS : S.Finite) {f : ℝ → X}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hmap : MapsTo f (Icc (0 : ℝ) 1) S) : f 0 = f 1 := by
  have hc : IsPreconnected (f '' Icc (0 : ℝ) 1) := isPreconnected_Icc.image f hf
  have hfin : (f '' Icc (0 : ℝ) 1).Finite := hS.subset (image_subset_iff.mpr hmap)
  by_contra hne
  exact hc.infinite_of_nontrivial
    ⟨f 0,mem_image_of_mem f (by norm_num),f 1,mem_image_of_mem f (by norm_num),hne⟩ hfin

theorem CylindricalTower.halfRoofSection_continuousOn {ρ : Type} {n : ℕ}
    {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S)
    (hβ : ContinuousOn β P) (hpos : ∀ p ∈ P, 0 < β p) :
    ContinuousOn c.halfRoofSection P := by
  have hpair : ContinuousOn (fun p => Sum.elim p (fun _ : Unit => β p/2)) P := by
    apply continuousOn_pi.mpr
    intro i
    cases i with
    | inl a => exact (continuous_apply a).continuousOn
    | inr a => exact hβ.div_const 2
  have hmap : MapsTo (fun p => Sum.elim p (fun _ : Unit => β p/2)) P
      (cadInitialBand P β) := by
    intro p hp
    exact ⟨hp,half_pos (hpos p hp),by change β p/2 < β p; linarith [hpos p hp]⟩
  exact continuousOn_pi.mpr (fun i => (continuous_apply _).comp_continuousOn
    (c.sectionMap_continuousOn.comp hpair hmap))

def CylindricalInitialBandDecomposition.finiteFiberSection
    {ρ : Type} {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E))
    (j : d.slicedLeaf) : (ρ → ℝ) → Fin n → ℝ :=
  (d.tower j.val.1 j.val.2).halfRoofSection

theorem CylindricalInitialBandDecomposition.finiteFiberSection_continuousOn
    {ρ : Type} {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) (j : d.slicedLeaf) :
    ContinuousOn (d.finiteFiberSection j) (d.base j.val.1) :=
  (d.tower j.val.1 j.val.2).halfRoofSection_continuousOn
    (d.roof j.val.1).continuousOn (d.roof_positive j.val.1)

theorem CylindricalInitialBandDecomposition.finiteFiberSection_graph
    {ρ : Type} [Finite ρ] {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) (j : d.slicedLeaf) :
    (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph (d.base j.val.1) (d.finiteFiberSection j)) :=
  (d.tower j.val.1 j.val.2).halfRoofSection_graph
    (d.roof j.val.1).graph_definable (d.roof_positive j.val.1)

theorem CylindricalInitialBandDecomposition.finiteFiberSection_mem
    {ρ : Type} {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) (j : d.slicedLeaf)
    {p : ρ → ℝ} (hp : p ∈ d.base j.val.1) :
    d.finiteFiberSection j p ∈ projectionFiber (d.slicedFiberCell j) p := by
  let c := d.tower j.val.1 j.val.2
  let v := Sum.elim p (fun _ : Unit => (d.roof j.val.1).value p/2)
  let w := c.sectionMap v
  have hproj : w ∘ cadBaseCoordinate n = v := c.sectionMap_projection v
  have hb : cadDropTime n w ∘ cadBaseCoordinate n = p := by
    rw [cadDropTime_base,hproj]; rfl
  have hout : cadDropTime n w ∘ cadOutputCoordinate n = d.finiteFiberSection j p := by
    funext i
    change w (cadKeepCoordinate n (cadOutputCoordinate n i)) = w (cadOutputCoordinate n i)
    rw [cadKeepCoordinate_output]
  have hpack : cadPack n p (d.finiteFiberSection j p) = cadDropTime n w := by
    have h := cadPack_reconstruct n (cadDropTime n w)
    rwa [hb,hout] at h
  change cadPack n p (d.finiteFiberSection j p) ∈ d.slicedCell j
  rw [hpack]
  refine ⟨hb.symm ▸ hp,?_⟩
  change cadInsertTime n (cadDropTime n w)
    ((d.roof j.val.1).value (cadDropTime n w ∘ cadBaseCoordinate n)/2) ∈ _
  rw [hb]
  have ht : w (cadBaseCoordinate n (Sum.inr ())) = (d.roof j.val.1).value p/2 :=
    congrFun hproj (Sum.inr ())
  rw [← ht,cadInsertTime_drop]
  apply c.sectionMap_mem
  have hpos := d.roof_positive j.val.1 p hp
  exact ⟨hp,by dsimp [v]; linarith,by dsimp [v]; linarith⟩

theorem CylindricalInitialBandDecomposition.finiteFiber_eq_section
    {ρ : Type} {n : ℕ} {P : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P (cadTimeCylinder n E)) (j : d.slicedLeaf)
    {p : ρ → ℝ} (hfin : (projectionFiber (cadPackedRelation n E) p).Finite)
    {x : Fin n → ℝ} (hx : x ∈ projectionFiber (d.slicedFiberCell j) p) :
    x = d.finiteFiberSection j p := by
  have hp : p ∈ d.base j.val.1 := by
    have h := hx.1
    simpa only [cadPack_base] using h
  have hmem := d.finiteFiberSection_mem j hp
  have hpath := (d.tower j.val.1 j.val.2).slicedFiberPath_properties hx hmem
  have he := finite_continuous_path_endpoints_eq hfin hpath.1
    (fun t ht => d.slicedFiberCell_subset j p (hpath.2.1 ht))
  simpa only [hpath.2.2.1,hpath.2.2.2] using he

end PaperI
