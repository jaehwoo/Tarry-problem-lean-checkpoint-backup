import PaperILean.ConnectedHardtPathGraphAssembly

/-! Explicit qualitative published inputs for manuscript I649/I654.

Basu--Pollack--Roy, second edition, Theorems 5.22--5.23 (printed p.168)
give connected semialgebraic sets semialgebraic paths. No analytic assertion or
uniform format is included in that input.

Theorem 5.46 (printed p.185) gives compatible semialgebraic Hardt charts for
finitely many marked subsets. We retain their actual graphs and compatibility
between different parameter fibers. The reference chart need not be the
identity; `referenceEndpoint` explicitly inverts it. Identifying the model
fiber with one actual fiber is the usual restriction of a trivialization.

The uniform path-format conclusion below is a project proof: choose finitely
many reference paths, transport through the charts, form the finite graph
union, apply qualitative QE, and specialize its finite polynomial family.
No external input supplies that uniform conclusion. -/

noncomputable section
namespace PaperI

structure PublishedSemialgebraicPathConnectedness : Prop where
  path : ∀ {κ : Type} [Finite κ] (S : Set (κ → ℝ)),
    HasPolynomialSignDescription S → IsPreconnected S →
    ∀ a ∈ S, ∀ b ∈ S, Nonempty (SemialgebraicUnitPath S a b)

structure PublishedCompatibleSemialgebraicHardtTriviality : Prop where
  projection_trivialization : ∀ {ρ κ : Type} [Finite ρ] [Finite κ]
    (A : Set ((ρ ⊕ κ) → ℝ)) (mark : Fin 2 → Set ((ρ ⊕ κ) → ℝ)),
    HasPolynomialSignDescription A →
    HasPolynomialSignDescription (projectionDomain A) →
    (∀ j, HasPolynomialSignDescription (mark j)) →
    (∀ j, mark j ⊆ A) → Nonempty (CompatibleProjectionHardtData A mark)

/-- Both endpoint sections are allowed to vary with all base parameters.
Their exact graph and membership are supplied locally. The common count and
degree precede all base valuations, rather than being chosen for each path. -/
theorem published_marked_family_uniform_path_format
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Finite κ]
    (A : Set ((ρ ⊕ κ) → ℝ)) (hA : HasPolynomialSignDescription A)
    (e : Fin 2 → (ρ → ℝ) → κ → ℝ)
    (hE : ∀ j, HasPolynomialSignDescription (endpointGraph A (e j)))
    (he : ∀ j p, p ∈ projectionDomain A → e j p ∈ projectionFiber A p) :
    ∃ s d : ℕ, ∀ p ∈ projectionDomain A, IsPreconnected (projectionFiber A p) →
      ∃ δ : SemialgebraicUnitPath (projectionFiber A p) (e 0 p) (e 1 p),
      ∃ B : Finset (MvPolynomial (Unit ⊕ κ) ℝ), B.card ≤ s ∧
        (∀ q ∈ B, q.totalDegree ≤ d) ∧
        PolynomialSignDetermined B (unitPathGraph δ.toFun) := by
  have hdom := published_real_projection_has_sign_description hQE
    (hasPolynomialSignDescription_definable hA)
  have hsub : ∀ j, endpointGraph A (e j) ⊆ A := by
    intro j v hv
    have h := he j _ hv.1
    change Sum.elim (fun r => v (Sum.inl r))
      (e j (fun r => v (Sum.inl r))) ∈ A at h
    rw [← hv.2] at h
    have heq : Sum.elim (fun r => v (Sum.inl r)) (fun k => v (Sum.inr k)) = v := by
      funext q
      cases q <;> rfl
    rwa [heq] at h
  obtain ⟨D⟩ := hHardt.projection_trivialization A
    (fun j => endpointGraph A (e j)) hA hdom hE hsub
  have href (i : ConnectedHardtIndex D.toProjectionHardtData) :=
    hPath.path _ (D.fiber_semialgebraic i.val) i.property
      (D.referenceEndpoint e he i.val 0).val (D.referenceEndpoint e he i.val 0).property
      (D.referenceEndpoint e he i.val 1).val (D.referenceEndpoint e he i.val 1).property
  let γ := fun i => Classical.choice (href i)
  exact D.uniform_connected_path_sign_format hQE e he γ

end PaperI
