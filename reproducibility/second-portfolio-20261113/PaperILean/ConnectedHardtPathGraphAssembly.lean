import PaperILean.HardtPathGraphAssembly

/-! Restrict to the finite subcollection of charts with connected reference
fibers. No definability premise for the connected-parameter locus is needed.
The final connectedness hypothesis follows the common bound and parameter. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def ConnectedHardtIndex {ρ κ : Type*} {A : Set ((ρ ⊕ κ) → ℝ)}
    (D : ProjectionHardtData A) :=
  {i : Fin D.n // IsPreconnected (projectionFiber A (D.basePoint i).val)}

instance instFintypeConnectedHardtIndex {ρ κ : Type*} {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A) :
    Fintype (ConnectedHardtIndex D) := by
  unfold ConnectedHardtIndex
  exact Fintype.ofFinite _

theorem ProjectionHardtData.reference_preconnected {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (p : D.piece i) (hc : IsPreconnected (projectionFiber A p.val)) :
    IsPreconnected (projectionFiber A (D.basePoint i).val) := by
  letI : PreconnectedSpace (projectionFiber A p.val) := Subtype.preconnectedSpace hc
  apply isPreconnected_iff_preconnectedSpace.mpr
  have h := (D.fiberHomeomorph i p).symm.isPreconnected_image.mpr
    (isPreconnected_univ : IsPreconnected (univ : Set (projectionFiber A p.val)))
  have hu : (D.fiberHomeomorph i p).symm '' univ = univ :=
    Set.image_univ_of_surjective (D.fiberHomeomorph i p).symm.surjective
  rw [hu] at h
  exact preconnectedSpace_iff_univ.mpr h

def connectedHardtPathGraphUnion {ρ κ : Type*} {A : Set ((ρ ⊕ κ) → ℝ)}
    (D : ProjectionHardtData A) (γ : ConnectedHardtIndex D → ℝ → κ → ℝ) :
    Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ) :=
  ⋃ i : ConnectedHardtIndex D, hardtTransportGraph D i.val (γ i)

theorem connectedHardtPathGraphUnion_definable {ρ κ : Type*} [Finite ρ] [Finite κ]
    {A : Set ((ρ ⊕ κ) → ℝ)} {mark : Fin 2 → Set ((ρ ⊕ κ) → ℝ)}
    (D : CompatibleProjectionHardtData A mark)
    (a b : ConnectedHardtIndex D.toProjectionHardtData → κ → ℝ)
    (γ : ∀ i, SemialgebraicUnitPath (projectionFiber A (D.basePoint i.val).val) (a i) (b i)) :
    (univ : Set ℝ).Definable Language.ring
      (connectedHardtPathGraphUnion D.toProjectionHardtData (fun i => (γ i).toFun)) := by
  simpa only [connectedHardtPathGraphUnion, Finset.mem_univ, iUnion_true] using
    (Set.definable_finset_biUnion
      (fun i => hardtTransportGraph_definable D i.val (γ i)) Finset.univ)

theorem connectedHardtPathGraphUnion_fiber {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (a b : ConnectedHardtIndex D → κ → ℝ)
    (γ : ∀ i, SemialgebraicUnitPath (projectionFiber A (D.basePoint i.val).val) (a i) (b i))
    (i : ConnectedHardtIndex D) (p : D.piece i.val) :
    projectionFiber (connectedHardtPathGraphUnion D (fun j => (γ j).toFun)) p.val =
      unitPathGraph (D.transportPath i.val p (γ i)) := by
  ext v
  have hv : Sum.elim (fun _ : Unit => v (Sum.inl ()))
      (fun k => v (Sum.inr k)) = v := by
    funext a
    rcases a with ⟨⟩ | a <;> rfl
  change Sum.elim p.val v ∈ connectedHardtPathGraphUnion D (fun j => (γ j).toFun) ↔ _
  rw [← hv]
  simp only [connectedHardtPathGraphUnion, mem_iUnion, hardtTransportGraph_mem_iff,
    unitPathGraph_mem_iff]
  constructor
  · rintro ⟨j, hpj, ht, hy⟩
    have hji : j = i := by
      apply Subtype.ext
      by_contra hne
      exact Set.disjoint_left.mp (D.disjoint hne) hpj p.property
    subst j
    exact ⟨ht, hy⟩
  · rintro ⟨ht, hy⟩
    exact ⟨i, p.property, ht, hy⟩

theorem CompatibleProjectionHardtData.uniform_connected_path_sign_format
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Finite κ] {A : Set ((ρ ⊕ κ) → ℝ)}
    (e : Fin 2 → (ρ → ℝ) → κ → ℝ)
    (D : CompatibleProjectionHardtData A (fun j => endpointGraph A (e j)))
    (he : ∀ j p, p ∈ projectionDomain A → e j p ∈ projectionFiber A p)
    (γ : ∀ i : ConnectedHardtIndex D.toProjectionHardtData,
      SemialgebraicUnitPath (projectionFiber A (D.basePoint i.val).val)
        (D.referenceEndpoint e he i.val 0).val (D.referenceEndpoint e he i.val 1).val) :
    ∃ s d : ℕ, ∀ p ∈ projectionDomain A, IsPreconnected (projectionFiber A p) →
      ∃ δ : SemialgebraicUnitPath (projectionFiber A p) (e 0 p) (e 1 p),
      ∃ B : Finset (MvPolynomial (Unit ⊕ κ) ℝ), B.card ≤ s ∧
        (∀ q ∈ B, q.totalDegree ≤ d) ∧ PolynomialSignDetermined B (unitPathGraph δ.toFun) := by
  let a := fun i : ConnectedHardtIndex D.toProjectionHardtData =>
    (D.referenceEndpoint e he i.val 0).val
  let b := fun i : ConnectedHardtIndex D.toProjectionHardtData =>
    (D.referenceEndpoint e he i.val 1).val
  have hG := hQE.finite_sign_description _ (connectedHardtPathGraphUnion_definable D a b γ)
  obtain ⟨s, d, hsd⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format hG
  refine ⟨s, d, ?_⟩
  intro p hp hc
  obtain ⟨i, hi⟩ := D.cover p hp
  let j : ConnectedHardtIndex D.toProjectionHardtData :=
    ⟨i, D.toProjectionHardtData.reference_preconnected i ⟨p, hi⟩ hc⟩
  obtain ⟨B, hcard, hdeg, hB⟩ := hsd p
  have heq := connectedHardtPathGraphUnion_fiber D.toProjectionHardtData a b γ j ⟨p, hi⟩
  rw [heq] at hB
  have hend := D.transportPath_endpoints e he i ⟨p, hi⟩ (γ j)
  let δ : SemialgebraicUnitPath (projectionFiber A p) (e 0 p) (e 1 p) :=
    ⟨_, D.toProjectionHardtData.transportPath_continuousOn i ⟨p, hi⟩ (γ j),
      D.toProjectionHardtData.transportPath_mapsTo i ⟨p, hi⟩ (γ j),
      hend.1, hend.2, ⟨B, hB⟩⟩
  exact ⟨δ, B, hcard, hdeg, hB⟩

end PaperI
