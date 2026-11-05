import PaperILean.CylindricalCADInput
import PaperILean.FiniteCylindricalGerms

/-! Joint germs from the literal cylindrical-section construction. The only
published inputs are structural CAD and qualitative real QE. A single finite
cell is chosen for each base stratum, then its section is constructed locally.
Generic definable choice, Nash regularity, and Hardt are not theorem premises.
The relation uses strict coordinate boxes, as in the existing closure encoding;
the equivalent finite-product topology supplies the limit at the attachment. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def cadNearbyLift {ρ : Type} (n : ℕ) (P : Set (ρ → ℝ))
    (C : Set ((ρ ⊕ Fin n) → ℝ)) (a : (ρ → ℝ) → Fin n → ℝ) :
    Set (CADVariables (ρ ⊕ Unit) n → ℝ) :=
  {z | Sum.elim (z ∘ cadBaseCoordinate n) (z ∘ cadOutputCoordinate n) ∈ nearbyPointRelation P C a}

theorem cadNearbyLift_definable {ρ : Type} [Finite ρ] (n : ℕ)
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ Fin n) → ℝ)) (a : (ρ → ℝ) → Fin n → ℝ)
    (hC : (univ : Set ℝ).Definable Language.ring C)
    (ha : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P a)) :
    (univ : Set ℝ).Definable Language.ring (cadNearbyLift n P C a) := by
  have h := (nearbyPointRelation_definable P C a hC ha).preimage_comp
    (Sum.elim (cadBaseCoordinate n) (cadOutputCoordinate n))
  convert h using 1

theorem cadNearbyLift_nonempty_fiber {ρ : Type} (n : ℕ)
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ Fin n) → ℝ)) (a : (ρ → ℝ) → Fin n → ℝ)
    (hcl : ∀ p ∈ P, a p ∈ closure (projectionFiber C p)) :
    ∀ p ∈ P, ∀ t ∈ Ioo (0 : ℝ) 1,
      ∃ x : Fin n → ℝ, cadPack n (Sum.elim p (fun _ : Unit => t)) x ∈ cadNearbyLift n P C a := by
  intro p hp t ht
  have hdom : Sum.elim p (fun _ : Unit => t) ∈ projectionDomain (nearbyPointRelation P C a) := by
    rw [nearbyPointRelation_domain P C a hcl]
    exact ⟨hp,ht.1⟩
  obtain ⟨x,hx⟩ := hdom
  refine ⟨x,?_⟩
  change Sum.elim (cadPack n (Sum.elim p (fun _ : Unit => t)) x ∘ cadBaseCoordinate n)
    (cadPack n (Sum.elim p (fun _ : Unit => t)) x ∘ cadOutputCoordinate n) ∈ nearbyPointRelation P C a
  rwa [cadPack_base,cadPack_output]

theorem cadNearbyLift_mem {ρ : Type} {n : ℕ}
    {P : Set (ρ → ℝ)} {C : Set ((ρ ⊕ Fin n) → ℝ)} {a : (ρ → ℝ) → Fin n → ℝ}
    {z : CADVariables (ρ ⊕ Unit) n → ℝ} (hz : z ∈ cadNearbyLift n P C a) :
    z ∘ cadOutputCoordinate n ∈ projectionFiber C (z ∘ cadBaseCoordinate n ∘ Sum.inl) ∧
      ∀ k, |z (cadOutputCoordinate n k) - a (z ∘ cadBaseCoordinate n ∘ Sum.inl) k| <
        z (cadBaseCoordinate n (Sum.inr ())) := hz.2.2

/-- The family is constructed from the ambient family and its closure-point
section. No supplied joint germ graph is a premise. All real parameters are
kept in the CAD base, and only time continuity is concluded. -/
theorem published_cylindrical_joint_curve_selection
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ)
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ Fin n) → ℝ)) (a : (ρ → ℝ) → Fin n → ℝ)
    (hC : HasPolynomialSignDescription C)
    (ha : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hcl : ∀ p ∈ P, a p ∈ closure (projectionFiber C p)) :
    ∃ (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → Fin n → ℝ),
      HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph P ε g) ∧
      ∀ p ∈ P, 0 < ε p ∧ g p 0 = a p ∧
        ContinuousOn (g p) (Ico (0 : ℝ) (ε p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) (ε p)) (projectionFiber C p) := by
  classical
  have haD := hasPolynomialSignDescription_definable ha
  have hPD := selectedFunctionGraph_domain_definable P a haD
  have hE := hQE.finite_sign_description _
    (cadNearbyLift_definable n P C a (hasPolynomialSignDescription_definable hC) haD)
  obtain ⟨d⟩ := hCAD.decomposition n P (cadNearbyLift n P C a) (hQE.finite_sign_description P hPD) hE
  have hcell : ∀ i : Fin d.count, ∃ j, d.cell i j ⊆ cadNearbyLift n P C a :=
    d.exists_cell_subset (cadNearbyLift_nonempty_fiber n P C a hcl)
  choose leaf hleaf using hcell
  have hlocal : ∀ i : Fin d.count, ∃ g : (ρ → ℝ) → ℝ → Fin n → ℝ,
      (univ : Set ℝ).Definable Language.ring (jointCurveGermGraph (d.base i) (d.roof i).value g) ∧
      ∀ p ∈ d.base i, g p 0 = a p ∧
        ContinuousOn (g p) (Ico (0 : ℝ) ((d.roof i).value p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) ((d.roof i).value p)) (projectionFiber C p) := by
    intro i
    exact cylindricalTower_joint_germ (d.base i) (d.roof i).value C a
      (d.roof i).graph_definable
      (cad_selectedGraph_restrict (d.base_subset i) a (d.base_definable i) haD)
      (d.roof_positive i) (d.tower i (leaf i)) (cadOutputCoordinate n)
      (fun z hz => cadNearbyLift_mem (hleaf i hz))
  choose g hg hprops using hlocal
  obtain ⟨ε,γ,hε,hγ,h⟩ := finite_cylindrical_germs_glue P d.base d.base_subset d.base_cover
    d.base_disjoint C a (fun i => (d.roof i).value) g (fun i => (d.roof i).graph_definable) hg
    (fun i p hp => ⟨d.roof_positive i p hp,hprops i p hp⟩)
  exact ⟨ε,γ,hQE.finite_sign_description _ hε,hQE.finite_sign_description _ hγ,h⟩

end PaperI
