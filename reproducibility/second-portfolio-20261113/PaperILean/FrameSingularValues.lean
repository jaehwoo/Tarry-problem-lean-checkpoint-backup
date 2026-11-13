import PaperILean.MatrixFrameFirstVariation
import Mathlib.Data.Fin.Tuple.Sort

/-! I303,311-315: Euclidean singular values, with multiplicity.
These are the positive square roots of the eigenvalues of B^T B.
The prescribed list is related by a permutation, not by set equality.
No Gram representation or singular-value decomposition is built into the definition. -/
noncomputable section
open scoped Matrix
namespace PaperI

def frameSingularValues (B : PositiveFrame) (i : Fin 3) : ℝ :=
  Real.sqrt ((frame_rightGram_posDef B).isHermitian.eigenvalues i)

def HasFrameSingularValues (B : PositiveFrame) (e : Fin 3 → ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), ∀ i, e i = frameSingularValues B (σ i)

theorem frameSingularValues_pos (B : PositiveFrame) (i : Fin 3) :
    0 < frameSingularValues B i :=
  Real.sqrt_pos.mpr ((frame_rightGram_posDef B).eigenvalues_pos i)

theorem frameSingularValues_sq (B : PositiveFrame) (i : Fin 3) :
    (frameSingularValues B i)^2 = (frame_rightGram_posDef B).isHermitian.eigenvalues i :=
  Real.sq_sqrt ((frame_rightGram_posDef B).eigenvalues_pos i).le

theorem hasFrameSingularValues_self (B : PositiveFrame) :
    HasFrameSingularValues B (frameSingularValues B) :=
  ⟨Equiv.refl _, fun _ => rfl⟩

theorem hasFrameSingularValues_pos (B : PositiveFrame) (e : Fin 3 → ℝ)
    (h : HasFrameSingularValues B e) : ∀ i, 0 < e i := by
  obtain ⟨σ, hσ⟩ := h
  intro i
  rw [hσ i]
  exact frameSingularValues_pos B (σ i)

theorem hasFrameSingularValues_sq (B : PositiveFrame) (e : Fin 3 → ℝ)
    (h : HasFrameSingularValues B e) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i,
      (e i)^2 = (frame_rightGram_posDef B).isHermitian.eigenvalues (σ i) := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ, fun i => by rw [hσ i, frameSingularValues_sq]⟩

theorem hasFrameSingularValues_iff_sq (B : PositiveFrame) (e : Fin 3 → ℝ) :
    HasFrameSingularValues B e ↔
      (∀ i, 0 ≤ e i) ∧ ∃ σ : Equiv.Perm (Fin 3), ∀ i,
        (e i)^2 = (frame_rightGram_posDef B).isHermitian.eigenvalues (σ i) := by
  constructor
  · intro h
    exact ⟨fun i => (hasFrameSingularValues_pos B e h i).le,
      hasFrameSingularValues_sq B e h⟩
  · rintro ⟨he, σ, hσ⟩
    refine ⟨σ, fun i => ?_⟩
    unfold frameSingularValues
    rw [← hσ i, Real.sqrt_sq (he i)]

theorem hasFrameSingularValues_reindex (B : PositiveFrame) (e : Fin 3 → ℝ)
    (h : HasFrameSingularValues B e) (τ : Equiv.Perm (Fin 3)) :
    HasFrameSingularValues B (e ∘ τ) := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨τ.trans σ, fun i => hσ (τ i)⟩

theorem exists_ordered_frameSingularValues (B : PositiveFrame) :
    ∃ e : Fin 3 → ℝ, (∀ i, 0 < e i) ∧ e 0 ≤ e 1 ∧ e 1 ≤ e 2 ∧
      HasFrameSingularValues B e := by
  let σ := Tuple.sort (frameSingularValues B)
  let e := frameSingularValues B ∘ σ
  have hm : Monotone e := Tuple.monotone_sort (frameSingularValues B)
  exact ⟨e, fun i => frameSingularValues_pos B (σ i),
    hm (by decide : (0 : Fin 3) ≤ 1), hm (by decide : (1 : Fin 3) ≤ 2),
    ⟨σ, fun _ => rfl⟩⟩

end PaperI
