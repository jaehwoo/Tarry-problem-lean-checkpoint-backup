import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Finite-dimensional intersection input for the ordered singular-value
perturbation estimate in I600 and I693. -/
noncomputable section
open scoped InnerProductSpace
namespace PaperI

theorem orthonormal_flags_intersect {n : ℕ}
    (b c : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (i : Fin n) :
    ∃ x : EuclideanSpace ℝ (Fin n), x ≠ 0 ∧
      (∀ j, i < j → ⟪b j, x⟫_ℝ = 0) ∧
      (∀ j, j < i → ⟪c j, x⟫_ℝ = 0) := by
  classical
  let e : (Fin (i.val + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun z j => if h : j.val < i.val + 1 then z ⟨j.val, h⟩ else 0
      map_add' := by intros; ext j; dsimp; split <;> simp
      map_smul' := by intros; ext j; dsimp; split <;> simp }
  let T : (Fin (i.val + 1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    b.repr.symm.toLinearMap.comp ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap.comp e)
  have hcoord (z : Fin (i.val + 1) → ℝ) (j : Fin n) :
      b.repr (T z) j = if h : j.val < i.val + 1 then z ⟨j.val, h⟩ else 0 := by
    simp [T, e]
  have hT (z : Fin (i.val + 1) → ℝ) (hz : T z = 0) : z = 0 := by
    ext j
    let j' : Fin n := ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩
    have hj := hcoord z j'
    rw [hz] at hj
    simpa [j', j.isLt] using hj.symm
  let L : (Fin (i.val + 1) → ℝ) →ₗ[ℝ] (Fin i.val → ℝ) :=
    { toFun := fun z j => c.repr (T z) ⟨j.val, lt_trans j.isLt i.isLt⟩
      map_add' := by intros; ext j; simp
      map_smul' := by intros; ext j; simp }
  have hdim : Module.finrank ℝ (Fin i.val → ℝ) <
      Module.finrank ℝ (Fin (i.val + 1) → ℝ) := by simp
  obtain ⟨z, hz, hz0⟩ := (LinearMap.ker L).ne_bot_iff.mp
    (LinearMap.ker_ne_bot_of_finrank_lt hdim)
  have hL : L z = 0 := hz
  refine ⟨T z, fun h => hz0 (hT z h), ?_, ?_⟩
  · intro j hj
    rw [← b.repr_apply_apply, hcoord]
    have : ¬j.val < i.val + 1 := by omega
    simp [this]
  · intro j hj
    have hv := congrFun hL ⟨j.val, hj⟩
    simpa [L, OrthonormalBasis.repr_apply_apply] using hv

end PaperI
