import PaperILean.FiberFrontierRelation
import PaperILean.DefinableDistanceBands

/-! The actual frontier intersected with a Euclidean ball, not the frontier
of a clipped set. Radius nonnegativity is retained even for negative radii. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def planarLocalFrontier (S : Set (Fin 2 → ℝ)) (z : Fin 2 → ℝ) (R : ℝ) :
    Set (Fin 2 → ℝ) :=
  {x | x ∈ frontier S ∧ 0 ≤ R ∧ planarSquaredDist x z ≤ R^2}

def planarLocalFrontierFamily {ρ : Type*} (G : Set ((ρ ⊕ Fin 2) → ℝ)) :
    Set (((ρ ⊕ (Fin 2 ⊕ Unit)) ⊕ Fin 2) → ℝ) :=
  {v | v ∘ Sum.inr ∈ planarLocalFrontier
    (projectionFiber G (fun r => v (Sum.inl (Sum.inl r))))
    (fun i => v (Sum.inl (Sum.inr (Sum.inl i))))
    (v (Sum.inl (Sum.inr (Sum.inr ()))))}

theorem planarLocalFrontierFamily_fiber {ρ : Type*} (G : Set ((ρ ⊕ Fin 2) → ℝ))
    (p : ρ → ℝ) (z : Fin 2 → ℝ) (R : ℝ) :
    projectionFiber (planarLocalFrontierFamily G)
      (Sum.elim p (Sum.elim z (fun _ => R))) =
      planarLocalFrontier (projectionFiber G p) z R := rfl

theorem planarLocalFrontierFamily_definable {ρ : Type} [Finite ρ]
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (planarLocalFrontierFamily G) := by
  let β := (ρ ⊕ (Fin 2 ⊕ Unit)) ⊕ Fin 2
  let e : ρ ⊕ Fin 2 → β := Sum.elim (fun r => Sum.inl (Sum.inl r)) Sum.inr
  let q := planarSquaredDistPolynomial (Sum.inr : Fin 2 → β)
    (fun i => Sum.inl (Sum.inr (Sum.inl i)))
  let r : MvPolynomial β ℝ := MvPolynomial.X (Sum.inl (Sum.inr (Sum.inr ())))
  have h := ((fiberFrontierRelation_definable hG).preimage_comp e).inter
    ((realPolynomial_le_definable 0 r).inter (realPolynomial_le_definable q (r^2)))
  convert h using 1
  ext v
  simp only [planarLocalFrontierFamily, planarLocalFrontier, fiberFrontierRelation,
    mem_setOf_eq, mem_inter_iff, mem_preimage, q, r,
    planarSquaredDistPolynomial_eval, map_zero, map_pow, MvPolynomial.eval_X,
    e, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  rfl

theorem published_planarLocalFrontierFamily_uniform_format
    (hQE : PublishedRealSemialgebraicity) {ρ : Type} [Finite ρ]
    (G : Set ((ρ ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ s D : ℕ, ∀ (p : ρ → ℝ) (z : Fin 2 → ℝ) (R : ℝ),
      ∃ A : Finset (MvPolynomial (Fin 2) ℝ), A.card ≤ s ∧
        (∀ q ∈ A, q.totalDegree ≤ D) ∧
        PolynomialSignDetermined A (planarLocalFrontier (projectionFiber G p) z R) := by
  obtain ⟨s, D, h⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format
    (hQE.finite_sign_description _ (planarLocalFrontierFamily_definable hG))
  exact ⟨s, D, fun p z R => h (Sum.elim p (Sum.elim z (fun _ => R)))⟩

end PaperI
