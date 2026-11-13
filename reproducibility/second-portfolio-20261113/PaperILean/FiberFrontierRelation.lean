import PaperILean.FiberClosureRelation

/-! I1261 prerequisite: take the frontier with the coefficient parameters fixed.
This is not the frontier of the total family. No arc decomposition is asserted. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def fiberFrontierRelation {ρ κ : Type*} (C : Set ((ρ ⊕ κ) → ℝ)) :
    Set ((ρ ⊕ κ) → ℝ) :=
  {v | v ∘ Sum.inr ∈ frontier (projectionFiber C (v ∘ Sum.inl))}

theorem fiberFrontierRelation_fiber {ρ κ : Type*}
    (C : Set ((ρ ⊕ κ) → ℝ)) (p : ρ → ℝ) :
    projectionFiber (fiberFrontierRelation C) p = frontier (projectionFiber C p) := rfl

theorem projectionFiber_compl {ρ κ : Type*}
    (C : Set ((ρ ⊕ κ) → ℝ)) (p : ρ → ℝ) :
    projectionFiber Cᶜ p = (projectionFiber C p)ᶜ := rfl

theorem fiberFrontierRelation_eq {ρ κ : Type*} (C : Set ((ρ ⊕ κ) → ℝ)) :
    fiberFrontierRelation C = fiberClosureRelation C ∩ fiberClosureRelation Cᶜ := by
  ext v
  simp only [fiberFrontierRelation, fiberClosureRelation, mem_setOf_eq, mem_inter_iff,
    frontier_eq_closure_inter_closure, projectionFiber_compl]

theorem fiberFrontierRelation_definable {ρ κ : Type} [Finite ρ] [Fintype κ]
    {C : Set ((ρ ⊕ κ) → ℝ)}
    (hC : (univ : Set ℝ).Definable Language.ring C) :
    (univ : Set ℝ).Definable Language.ring (fiberFrontierRelation C) := by
  rw [fiberFrontierRelation_eq]
  exact (fiberClosureRelation_definable hC).inter
    (fiberClosureRelation_definable hC.compl)

theorem published_fiberFrontierRelation_semialgebraic
    (hQE : PublishedRealSemialgebraicity) {ρ κ : Type} [Finite ρ] [Fintype κ]
    {C : Set ((ρ ⊕ κ) → ℝ)} (hC : HasPolynomialSignDescription C) :
    HasPolynomialSignDescription (fiberFrontierRelation C) :=
  hQE.finite_sign_description _
    (fiberFrontierRelation_definable (hasPolynomialSignDescription_definable hC))

/-- The output bounds precede all coefficient valuations, including degenerate fibers. -/
theorem published_fiberFrontierRelation_uniform_format
    (hQE : PublishedRealSemialgebraicity) {ρ κ : Type} [Finite ρ] [Fintype κ]
    (C : Set ((ρ ⊕ κ) → ℝ))
    (hC : (univ : Set ℝ).Definable Language.ring C) :
    ∃ s D : ℕ, ∀ p : ρ → ℝ,
      ∃ A : Finset (MvPolynomial κ ℝ), A.card ≤ s ∧
        (∀ q ∈ A, q.totalDegree ≤ D) ∧
        PolynomialSignDetermined A (frontier (projectionFiber C p)) := by
  obtain ⟨s, D, h⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format
    (hQE.finite_sign_description _ (fiberFrontierRelation_definable hC))
  exact ⟨s, D, fun p => h p⟩

end PaperI
