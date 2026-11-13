import PaperILean.CellChartPathFamily
import PaperILean.JointUnitPathGraphs
import PaperILean.SelectedGraphMeasurability

/-! Actual chart-interpolation paths for jointly semialgebraic endpoint sections.
Charts are required only on their active parameter domain. Their joint graph
is an explicit premise, not inferred from pointwise cell decomposition.
Pre-strategy evidence: checkpoint_116_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable

def jointCubeChartGraph {ρ κ : Type*} {d : ℕ}
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ))
    (e : ∀ p : P, openUnitCube d ≃ₜ projectionFiber C p.val) :
    Set ((ρ ⊕ (Fin d ⊕ κ)) → ℝ) :=
  {z | ∃ hp : z ∘ Sum.inl ∈ P,
    z ∘ Sum.inr ∈ cubeMapGraph (fun u => (e ⟨_,hp⟩ u).val)}

theorem jointCubeChartGraph_fiber {ρ κ : Type*} {d : ℕ}
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ))
    (e : ∀ p : P, openUnitCube d ≃ₜ projectionFiber C p.val) (p : P) :
    projectionFiber (jointCubeChartGraph P C e) p.val =
      cubeMapGraph (fun u => (e p u).val) := by
  ext z
  exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨p.property,h⟩⟩

theorem jointCubeChartGraph_fiber_offDomain {ρ κ : Type*} {d : ℕ}
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ))
    (e : ∀ p : P, openUnitCube d ≃ₜ projectionFiber C p.val)
    {p : ρ → ℝ} (hp : p ∉ P) :
    projectionFiber (jointCubeChartGraph P C e) p = ∅ := by
  ext z
  exact ⟨fun ⟨h,_⟩ => (hp h).elim, fun h => h.elim⟩

def chartSectionPathRelation {ρ κ : Type*}
    (A B : Set ((ρ ⊕ κ) → ℝ))
    (H : Set ((ρ ⊕ ((κ ⊕ κ) ⊕ (Unit ⊕ κ))) → ℝ)) :
    Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ) :=
  {z | ∃ a b : κ → ℝ,
    Sum.elim (z ∘ Sum.inl) a ∈ A ∧ Sum.elim (z ∘ Sum.inl) b ∈ B ∧
    Sum.elim (z ∘ Sum.inl) (Sum.elim (Sum.elim a b) (z ∘ Sum.inr)) ∈ H}

theorem chartSectionPathRelation_definable {ρ κ : Type*} [Finite ρ] [Finite κ]
    {A B : Set ((ρ ⊕ κ) → ℝ)}
    {H : Set ((ρ ⊕ ((κ ⊕ κ) ⊕ (Unit ⊕ κ))) → ℝ)}
    (hA : (univ : Set ℝ).Definable Language.ring A)
    (hB : (univ : Set ℝ).Definable Language.ring B)
    (hH : (univ : Set ℝ).Definable Language.ring H) :
    (univ : Set ℝ).Definable Language.ring (chartSectionPathRelation A B H) := by
  let δ := ρ ⊕ (Unit ⊕ κ)
  let eA : ρ ⊕ κ → δ ⊕ (κ ⊕ κ) :=
    Sum.elim (fun r => Sum.inl (Sum.inl r)) (fun k => Sum.inr (Sum.inl k))
  let eB : ρ ⊕ κ → δ ⊕ (κ ⊕ κ) :=
    Sum.elim (fun r => Sum.inl (Sum.inl r)) (fun k => Sum.inr (Sum.inr k))
  let eH : ρ ⊕ ((κ ⊕ κ) ⊕ (Unit ⊕ κ)) → δ ⊕ (κ ⊕ κ) :=
    Sum.elim (fun r => Sum.inl (Sum.inl r))
      (Sum.elim Sum.inr (fun k => Sum.inl (Sum.inr k)))
  have h := realDefinable_exists
    ((hA.preimage_comp eA).inter ((hB.preimage_comp eB).inter (hH.preimage_comp eH)))
  convert h using 1
  ext z
  change (∃ a b, _ ∧ _ ∧ _) ↔ ∃ w : (κ ⊕ κ) → ℝ, _ ∧ _ ∧ _
  have heA (w : (κ ⊕ κ) → ℝ) :
      Sum.elim z w ∘ eA = Sum.elim (z ∘ Sum.inl) (w ∘ Sum.inl) := by
    funext i; cases i <;> rfl
  have heB (w : (κ ⊕ κ) → ℝ) :
      Sum.elim z w ∘ eB = Sum.elim (z ∘ Sum.inl) (w ∘ Sum.inr) := by
    funext i; cases i <;> rfl
  have heH (w : (κ ⊕ κ) → ℝ) :
      Sum.elim z w ∘ eH = Sum.elim (z ∘ Sum.inl) (Sum.elim w (z ∘ Sum.inr)) := by
    funext i; rcases i with i | (i | i) <;> rfl
  simp only [mem_preimage, heA, heB, heH]
  constructor
  · rintro ⟨a,b,ha,hb,hh⟩
    exact ⟨Sum.elim a b,ha,hb,hh⟩
  · rintro ⟨w,ha,hb,hh⟩
    refine ⟨w ∘ Sum.inl,w ∘ Sum.inr,ha,hb,?_⟩
    have hw : Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) = w := by
      funext i; cases i <;> rfl
    rwa [hw]

def cellChartSectionPath {ρ κ : Type*} {d : ℕ}
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ))
    (e : ∀ p : P, openUnitCube d ≃ₜ projectionFiber C p.val)
    (a b : (ρ → ℝ) → κ → ℝ)
    (ha : ∀ p ∈ P, a p ∈ projectionFiber C p)
    (hb : ∀ p ∈ P, b p ∈ projectionFiber C p) (p : ρ → ℝ) : ℝ → κ → ℝ :=
  if hp : p ∈ P then cellChartPath (e ⟨p,hp⟩) ⟨a p,ha p hp⟩ ⟨b p,hb p hp⟩ else 0

theorem cellChartSectionPath_on_domain {ρ κ : Type*} {d : ℕ}
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ))
    (e : ∀ p : P, openUnitCube d ≃ₜ projectionFiber C p.val)
    (a b : (ρ → ℝ) → κ → ℝ)
    (ha : ∀ p ∈ P, a p ∈ projectionFiber C p)
    (hb : ∀ p ∈ P, b p ∈ projectionFiber C p) {p : ρ → ℝ} (hp : p ∈ P) :
    cellChartSectionPath P C e a b ha hb p =
      cellChartPath (e ⟨p,hp⟩) ⟨a p,ha p hp⟩ ⟨b p,hb p hp⟩ := by
  simp only [cellChartSectionPath, dif_pos hp]

theorem cellChartSectionPath_properties {ρ κ : Type*} {d : ℕ}
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ))
    (e : ∀ p : P, openUnitCube d ≃ₜ projectionFiber C p.val)
    (a b : (ρ → ℝ) → κ → ℝ)
    (ha : ∀ p ∈ P, a p ∈ projectionFiber C p)
    (hb : ∀ p ∈ P, b p ∈ projectionFiber C p) {p : ρ → ℝ} (hp : p ∈ P) :
    ContinuousOn (cellChartSectionPath P C e a b ha hb p) (Icc (0 : ℝ) 1) ∧
    MapsTo (cellChartSectionPath P C e a b ha hb p) (Icc (0 : ℝ) 1) (projectionFiber C p) ∧
    cellChartSectionPath P C e a b ha hb p 0 = a p ∧
    cellChartSectionPath P C e a b ha hb p 1 = b p := by
  rw [cellChartSectionPath_on_domain P C e a b ha hb hp]
  exact ⟨cellChartPath_continuousOn _ _ _,cellChartPath_mapsTo _ _ _,
    cellChartPath_source _ _ _,cellChartPath_target _ _ _⟩

theorem cellChartSectionPath_joint_graph {ρ κ : Type*} {d : ℕ}
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ))
    (e : ∀ p : P, openUnitCube d ≃ₜ projectionFiber C p.val)
    (a b : (ρ → ℝ) → κ → ℝ)
    (ha : ∀ p ∈ P, a p ∈ projectionFiber C p)
    (hb : ∀ p ∈ P, b p ∈ projectionFiber C p) :
    jointUnitPathGraph P (cellChartSectionPath P C e a b ha hb) =
      chartSectionPathRelation (selectedFunctionGraph P a) (selectedFunctionGraph P b)
        (cubeChartPathRelationFamily (jointCubeChartGraph P C e)) := by
  ext z
  let p := z ∘ Sum.inl
  by_cases hp : p ∈ P
  · have h := cubeChartPathRelation_chart_mem (e ⟨p,hp⟩)
      ⟨a p,ha p hp⟩ ⟨b p,hb p hp⟩ (z (Sum.inr (Sum.inl ())))
      (fun k => z (Sum.inr (Sum.inr k)))
    have hz : Sum.elim (fun _ : Unit => z (Sum.inr (Sum.inl ())))
        (fun k => z (Sum.inr (Sum.inr k))) = z ∘ Sum.inr := by
      funext i; rcases i with ⟨⟩ | i <;> rfl
    rw [hz] at h
    simp only [jointUnitPathGraph, chartSectionPathRelation, selectedFunctionGraph,
      mem_setOf_eq, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    change (p ∈ P ∧ _ ∈ unitPathGraph _) ↔ ∃ u v, (p ∈ P ∧ a p = u) ∧
      (p ∈ P ∧ b p = v) ∧ _
    simp only [hp,true_and]
    have hactual :
        Sum.elim p (Sum.elim (Sum.elim (a p) (b p)) (z ∘ Sum.inr)) ∈
          cubeChartPathRelationFamily (jointCubeChartGraph P C e) ↔
        z ∘ Sum.inr ∈ unitPathGraph (cellChartSectionPath P C e a b ha hb p) := by
      change Sum.elim (Sum.elim (a p) (b p)) (z ∘ Sum.inr) ∈
        cubeChartPathRelation (projectionFiber (jointCubeChartGraph P C e) p) ↔ _
      rw [jointCubeChartGraph_fiber P C e ⟨p,hp⟩]
      rw [h,cellChartSectionPath_on_domain P C e a b ha hb hp]
      rfl
    constructor
    · intro hz
      exact ⟨a p,b p,rfl,rfl,hactual.mpr hz⟩
    · rintro ⟨u,v,hu,hv,hpath⟩
      subst u v
      exact hactual.mp hpath
  · simp only [jointUnitPathGraph, chartSectionPathRelation, selectedFunctionGraph,
      mem_setOf_eq, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    change (p ∈ P ∧ _) ↔ ∃ u v, (p ∈ P ∧ _) ∧ _
    simp only [hp,false_and,exists_false]

theorem published_cellChartSectionPath_joint_semialgebraic
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Finite κ] {d : ℕ}
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ))
    (e : ∀ p : P, openUnitCube d ≃ₜ projectionFiber C p.val)
    (a b : (ρ → ℝ) → κ → ℝ)
    (ha : ∀ p ∈ P, a p ∈ projectionFiber C p)
    (hb : ∀ p ∈ P, b p ∈ projectionFiber C p)
    (hG : HasPolynomialSignDescription (jointCubeChartGraph P C e))
    (hA : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hB : HasPolynomialSignDescription (selectedFunctionGraph P b)) :
    HasPolynomialSignDescription (jointUnitPathGraph P (cellChartSectionPath P C e a b ha hb)) := by
  rw [cellChartSectionPath_joint_graph]
  exact hQE.finite_sign_description _ (chartSectionPathRelation_definable
    (hasPolynomialSignDescription_definable hA) (hasPolynomialSignDescription_definable hB)
    (cubeChartPathRelationFamily_definable (hasPolynomialSignDescription_definable hG)))

theorem published_cellChartSectionPath_bounded_unitPaths
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Finite κ] {d : ℕ}
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ))
    (e : ∀ p : P, openUnitCube d ≃ₜ projectionFiber C p.val)
    (a b : (ρ → ℝ) → κ → ℝ)
    (ha : ∀ p ∈ P, a p ∈ projectionFiber C p)
    (hb : ∀ p ∈ P, b p ∈ projectionFiber C p)
    (hG : HasPolynomialSignDescription (jointCubeChartGraph P C e))
    (hA : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hB : HasPolynomialSignDescription (selectedFunctionGraph P b)) :
    ∃ s dPath : ℕ, ∀ p ∈ P, ∃ γ : SemialgebraicUnitPath (projectionFiber C p) (a p) (b p),
      γ.toFun = cellChartSectionPath P C e a b ha hb p ∧
      ∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ), A.card ≤ s ∧
        (∀ q ∈ A, q.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  have hg := published_cellChartSectionPath_joint_semialgebraic hQE P C e a b ha hb hG hA hB
  obtain ⟨s,dPath,hfmt⟩ := jointUnitPathGraph_uniform_fiber_format P _ hg
  refine ⟨s,dPath,?_⟩
  intro p hp
  have h := cellChartSectionPath_properties P C e a b ha hb hp
  obtain ⟨A,hs,hd,hA⟩ := hfmt p hp
  exact ⟨⟨_,h.1,h.2.1,h.2.2.1,h.2.2.2,⟨A,hA⟩⟩,rfl,A,hs,hd,hA⟩

end PaperI
