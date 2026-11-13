import PaperILean.CellChartPathGraph

/-! The coefficient-parameterized chart-path relation. All three graph tests
use the same parameter vector and the same interpolation-coordinate witness.
This is a local bridge for I654; it does not construct a cell decomposition.
Pre-strategy checks: evidence/checkpoint_110_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def cubeChartPathRelationFamily {ρ α : Type*} {d : ℕ}
    (G : Set ((ρ ⊕ (Fin d ⊕ α)) → ℝ)) :
    Set ((ρ ⊕ ((α ⊕ α) ⊕ (Unit ⊕ α))) → ℝ) :=
  {x | x ∘ Sum.inr ∈ cubeChartPathRelation (projectionFiber G (x ∘ Sum.inl))}

theorem cubeChartPathRelationFamily_fiber {ρ α : Type*} {d : ℕ}
    (G : Set ((ρ ⊕ (Fin d ⊕ α)) → ℝ)) (p : ρ → ℝ) :
    projectionFiber (cubeChartPathRelationFamily G) p =
      cubeChartPathRelation (projectionFiber G p) := by
  ext x
  rfl

theorem cubeChartPathRelationFamily_definable {ρ α : Type*}
    [Finite ρ] [Finite α] {d : ℕ} {G : Set ((ρ ⊕ (Fin d ⊕ α)) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (cubeChartPathRelationFamily G) := by
  let δ := ρ ⊕ ((α ⊕ α) ⊕ (Unit ⊕ α))
  let β := Fin 3 × Fin d
  let e0 : ρ ⊕ (Fin d ⊕ α) → δ ⊕ β :=
    Sum.elim (fun r => Sum.inl (Sum.inl r))
      (Sum.elim (fun i => Sum.inr (0,i))
        (fun i => Sum.inl (Sum.inr (Sum.inl (Sum.inl i)))))
  let e1 : ρ ⊕ (Fin d ⊕ α) → δ ⊕ β :=
    Sum.elim (fun r => Sum.inl (Sum.inl r))
      (Sum.elim (fun i => Sum.inr (1,i))
        (fun i => Sum.inl (Sum.inr (Sum.inl (Sum.inr i)))))
  let e2 : ρ ⊕ (Fin d ⊕ α) → δ ⊕ β :=
    Sum.elim (fun r => Sum.inl (Sum.inl r))
      (Sum.elim (fun i => Sum.inr (2,i))
        (fun i => Sum.inl (Sum.inr (Sum.inr (Sum.inr i)))))
  let T : MvPolynomial (δ ⊕ β) ℝ :=
    MvPolynomial.X (Sum.inl (Sum.inr (Sum.inr (Sum.inl ()))))
  let Q (i : Fin d) : MvPolynomial (δ ⊕ β) ℝ :=
    MvPolynomial.X (Sum.inr (2,i)) -
      ((1-T)*MvPolynomial.X (Sum.inr (0,i)) + T*MvPolynomial.X (Sum.inr (1,i)))
  have hEq := realDefinable_finite_all (fun i : Fin d => realPolynomial_zero_definable (Q i))
  have h := realDefinable_exists
    (((hG.preimage_comp e0).inter ((hG.preimage_comp e1).inter (hG.preimage_comp e2))).inter hEq)
  have ht : (univ : Set ℝ).Definable Language.ring
      {x : δ → ℝ | x (Sum.inr (Sum.inr (Sum.inl ()))) ∈ Icc (0 : ℝ) 1} := by
    have h0 := realPolynomial_nonneg_definable
      (MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl ()))) : MvPolynomial δ ℝ)
    have h1 := realPolynomial_nonneg_definable
      (1 - MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl ()))) : MvPolynomial δ ℝ)
    simpa only [Set.inter_def, Set.mem_setOf_eq, MvPolynomial.eval_X, map_sub, map_one,
      sub_nonneg, Set.mem_Icc] using h0.inter h1
  convert ht.inter h using 1
  ext x
  change (_ ∧ ∃ w : β → ℝ, _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ ∃ w : β → ℝ, _)
  apply and_congr_right
  intro _
  apply exists_congr
  intro w
  have he0 : Sum.elim x w ∘ e0 = Sum.elim (x ∘ Sum.inl)
      (Sum.elim (fun i => w (0,i)) (fun i => x (Sum.inr (Sum.inl (Sum.inl i))))) := by
    funext i; rcases i with i | i; · rfl
    cases i <;> rfl
  have he1 : Sum.elim x w ∘ e1 = Sum.elim (x ∘ Sum.inl)
      (Sum.elim (fun i => w (1,i)) (fun i => x (Sum.inr (Sum.inl (Sum.inr i))))) := by
    funext i; rcases i with i | i; · rfl
    cases i <;> rfl
  have he2 : Sum.elim x w ∘ e2 = Sum.elim (x ∘ Sum.inl)
      (Sum.elim (fun i => w (2,i)) (fun i => x (Sum.inr (Sum.inr (Sum.inr i))))) := by
    funext i; rcases i with i | i; · rfl
    cases i <;> rfl
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, he0, he1, he2,
    Q, T, map_sub, map_add, map_mul, map_one, MvPolynomial.eval_X,
    Sum.elim_inl, Sum.elim_inr, sub_eq_zero, and_assoc, projectionFiber,
    Function.comp_apply]

end PaperI
