import PaperILean.MarkedHardtPathTransport
import PaperILean.SemialgebraicRelationComposition
import PaperILean.PublishedRealAlgebraicAssumptions

/-! A finite collection of reference paths is transported through the actual
Hardt charts. Their finite graph union is one semialgebraic relation, so one
polynomial count and degree bound precede every base parameter. The chart
compatibility and reference paths remain explicit data here. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def liftedUnitPathGraph {ρ κ : Type*} (γ : ℝ → κ → ℝ) :
    Set (((ρ ⊕ Unit) ⊕ κ) → ℝ) :=
  {v | v ∘ Sum.elim (fun u => Sum.inl (Sum.inr u)) Sum.inr ∈ unitPathGraph γ}

theorem liftedUnitPathGraph_definable {ρ κ : Type*} [Finite ρ] [Finite κ]
    {γ : ℝ → κ → ℝ} (hγ : HasPolynomialSignDescription (unitPathGraph γ)) :
    (univ : Set ℝ).Definable Language.ring (liftedUnitPathGraph (ρ := ρ) γ) :=
  (hasPolynomialSignDescription_definable hγ).preimage_comp _

def hardtTransportGraph {ρ κ : Type*} {A : Set ((ρ ⊕ κ) → ℝ)}
    (D : ProjectionHardtData A) (i : Fin D.n) (γ : ℝ → κ → ℝ) :
    Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ) :=
  relationGraphCompositionParametric (liftedUnitPathGraph γ) (D.chartGraph i)

theorem hardtTransportGraph_definable {ρ κ : Type*} [Finite ρ] [Finite κ]
    {A : Set ((ρ ⊕ κ) → ℝ)} {mark : Fin 2 → Set ((ρ ⊕ κ) → ℝ)}
    (D : CompatibleProjectionHardtData A mark) (i : Fin D.n)
    {a b : κ → ℝ}
    (γ : SemialgebraicUnitPath (projectionFiber A (D.basePoint i).val) a b) :
    (univ : Set ℝ).Definable Language.ring
      (hardtTransportGraph D.toProjectionHardtData i γ.toFun) :=
  relationGraphCompositionParametric_definable
    (liftedUnitPathGraph_definable γ.semialgebraic)
    (hasPolynomialSignDescription_definable (D.chart_semialgebraic i))

theorem hardtTransportGraph_mem_iff {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A) (i : Fin D.n)
    {a b : κ → ℝ}
    (γ : SemialgebraicUnitPath (projectionFiber A (D.basePoint i).val) a b)
    (p : ρ → ℝ) (t : ℝ) (y : κ → ℝ) :
    Sum.elim p (Sum.elim (fun _ => t) y) ∈ hardtTransportGraph D i γ.toFun ↔
      ∃ hp : p ∈ D.piece i, t ∈ Icc (0 : ℝ) 1 ∧
        y = D.transportPath i ⟨p, hp⟩ γ t := by
  rw [hardtTransportGraph, relationGraphCompositionParametric_mem]
  change (∃ x : κ → ℝ, (t ∈ Icc (0 : ℝ) 1 ∧ x = γ.toFun t) ∧
    ∃ (hp : p ∈ D.piece i) (hx : x ∈ projectionFiber A (D.basePoint i).val),
      y = (D.chart i (⟨p, hp⟩, ⟨x, hx⟩)).val.2) ↔ _
  constructor
  · rintro ⟨x, ⟨ht, rfl⟩, hp, hx, hy⟩
    exact ⟨hp, ht, hy.trans (D.transportPath_eq i ⟨p, hp⟩ γ ht).symm⟩
  · rintro ⟨hp, ht, hy⟩
    exact ⟨γ.toFun t, ⟨ht, rfl⟩, hp, γ.mapsTo ht,
      hy.trans (D.transportPath_eq i ⟨p, hp⟩ γ ht)⟩

def hardtPathGraphUnion {ρ κ : Type*} {A : Set ((ρ ⊕ κ) → ℝ)}
    (D : ProjectionHardtData A) (γ : Fin D.n → ℝ → κ → ℝ) :
    Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ) := ⋃ i, hardtTransportGraph D i (γ i)

theorem hardtPathGraphUnion_definable {ρ κ : Type*} [Finite ρ] [Finite κ]
    {A : Set ((ρ ⊕ κ) → ℝ)} {mark : Fin 2 → Set ((ρ ⊕ κ) → ℝ)}
    (D : CompatibleProjectionHardtData A mark) (a b : Fin D.n → κ → ℝ)
    (γ : ∀ i, SemialgebraicUnitPath (projectionFiber A (D.basePoint i).val) (a i) (b i)) :
    (univ : Set ℝ).Definable Language.ring
      (hardtPathGraphUnion D.toProjectionHardtData (fun i => (γ i).toFun)) := by
  simpa only [hardtPathGraphUnion, Finset.mem_univ, iUnion_true] using
    (Set.definable_finset_biUnion
      (fun i => hardtTransportGraph_definable D i (γ i)) Finset.univ)

theorem hardtPathGraphUnion_fiber {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (a b : Fin D.n → κ → ℝ)
    (γ : ∀ i, SemialgebraicUnitPath (projectionFiber A (D.basePoint i).val) (a i) (b i))
    (i : Fin D.n) (p : D.piece i) :
    projectionFiber (hardtPathGraphUnion D (fun j => (γ j).toFun)) p.val =
      unitPathGraph (D.transportPath i p (γ i)) := by
  ext v
  have hv : Sum.elim (fun _ : Unit => v (Sum.inl ()))
      (fun k => v (Sum.inr k)) = v := by
    funext a
    rcases a with ⟨⟩ | a <;> rfl
  change Sum.elim p.val v ∈ hardtPathGraphUnion D (fun j => (γ j).toFun) ↔ _
  rw [← hv]
  simp only [hardtPathGraphUnion, mem_iUnion, hardtTransportGraph_mem_iff,
    unitPathGraph_mem_iff]
  constructor
  · rintro ⟨j, hpj, ht, hy⟩
    have hji : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (D.disjoint hne) hpj p.property
    subst j
    exact ⟨ht, hy⟩
  · rintro ⟨ht, hy⟩
    exact ⟨i, p.property, ht, hy⟩

theorem CompatibleProjectionHardtData.uniform_path_sign_format
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Finite κ] {A : Set ((ρ ⊕ κ) → ℝ)}
    (e : Fin 2 → (ρ → ℝ) → κ → ℝ)
    (D : CompatibleProjectionHardtData A (fun j => endpointGraph A (e j)))
    (he : ∀ j p, p ∈ projectionDomain A → e j p ∈ projectionFiber A p)
    (γ : ∀ i, SemialgebraicUnitPath (projectionFiber A (D.basePoint i).val)
      (D.referenceEndpoint e he i 0).val (D.referenceEndpoint e he i 1).val) :
    ∃ s d : ℕ, ∀ p ∈ projectionDomain A,
      ∃ δ : SemialgebraicUnitPath (projectionFiber A p) (e 0 p) (e 1 p),
      ∃ B : Finset (MvPolynomial (Unit ⊕ κ) ℝ), B.card ≤ s ∧
        (∀ q ∈ B, q.totalDegree ≤ d) ∧ PolynomialSignDetermined B (unitPathGraph δ.toFun) := by
  let a := fun i => (D.referenceEndpoint e he i 0).val
  let b := fun i => (D.referenceEndpoint e he i 1).val
  have hG := hQE.finite_sign_description _ (hardtPathGraphUnion_definable D a b γ)
  obtain ⟨s, d, hsd⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format hG
  refine ⟨s, d, ?_⟩
  intro p hp
  obtain ⟨i, hi⟩ := D.cover p hp
  obtain ⟨B, hcard, hdeg, hB⟩ := hsd p
  have heq := hardtPathGraphUnion_fiber D.toProjectionHardtData a b γ i ⟨p, hi⟩
  rw [heq] at hB
  have hend := D.transportPath_endpoints e he i ⟨p, hi⟩ (γ i)
  let δ : SemialgebraicUnitPath (projectionFiber A p) (e 0 p) (e 1 p) :=
    ⟨_, D.toProjectionHardtData.transportPath_continuousOn i ⟨p, hi⟩ (γ i),
      D.toProjectionHardtData.transportPath_mapsTo i ⟨p, hi⟩ (γ i),
      hend.1, hend.2, ⟨B, hB⟩⟩
  exact ⟨δ, B, hcard, hdeg, hB⟩

end PaperI
