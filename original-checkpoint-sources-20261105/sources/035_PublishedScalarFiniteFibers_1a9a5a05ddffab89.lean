import PaperILean.PublishedUniformComponents

/-! A scalar finite-fiber consequence of the checked component/Hardt application.
The common integer is chosen before the parameter and before any proof that its
particular fiber is finite. Finiteness is a separate premise, never inferred
from `Nat.card`. Unit coordinates are explicitly identified with real numbers. -/

noncomputable section
namespace PaperI

def scalarProjectionFiber {ι : Type*} (A : Set ((ι ⊕ Unit) → ℝ))
    (p : ι → ℝ) : Set ℝ := {x | Sum.elim p (fun _ => x) ∈ A}

def projectionFiberUnitEquivScalar {ι : Type*} (A : Set ((ι ⊕ Unit) → ℝ))
    (p : ι → ℝ) : projectionFiber A p ≃ scalarProjectionFiber A p where
  toFun v := ⟨v.val (), by
    have hv : (fun _ : Unit => v.val ()) = v.val := by funext u; cases u; rfl
    simpa only [scalarProjectionFiber, Set.mem_setOf_eq, hv] using v.property⟩
  invFun x := ⟨fun _ => x.val, x.property⟩
  left_inv v := Subtype.ext (by funext u; cases u; rfl)
  right_inv _ := rfl

/-- Uniform scalar cardinality for the finite fibers of one fixed family. -/
theorem published_scalar_finite_fiber_card_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {ι : Type} [Finite ι]
    (A : Set ((ι ⊕ Unit) → ℝ)) (hA : HasPolynomialSignDescription A) :
    ∃ N : ℕ, ∀ p : ι → ℝ, (scalarProjectionFiber A p).Finite →
      Nat.card (scalarProjectionFiber A p) ≤ N := by
  obtain ⟨N, hN⟩ :=
    published_projection_totallyDisconnected_fiber_card_bound hCell hHardt hQE A hA
  refine ⟨N, ?_⟩
  intro p hp
  letI : Finite (scalarProjectionFiber A p) := hp.finite_toSet
  letI : Finite (projectionFiber A p) :=
    Finite.of_equiv (scalarProjectionFiber A p) (projectionFiberUnitEquivScalar A p).symm
  have hbound := (hN p inferInstance).2
  exact (Nat.card_congr (projectionFiberUnitEquivScalar A p)).symm.trans_le hbound

end PaperI
