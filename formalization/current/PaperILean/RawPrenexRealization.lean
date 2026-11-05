import PaperILean.QuantifiedPolynomialFormat
import Mathlib.ModelTheory.Complexity

/-! Extract an ordered scalar prefix from actual mathlib first-order syntax.
All newly quantified coordinates use one common bound assignment. The checked
`Fin.append` associativity identity reconciles prefix order with mathlib's
`Fin.snoc` bound-variable convention. No quantifier-elimination input occurs. -/

noncomputable section
namespace PaperI
open FirstOrder

theorem forall_scalar_tuple (P : ℝ → Prop) :
    (∀ x : Fin 1 → ℝ, P (x 0)) ↔ ∀ x : ℝ, P x :=
  ⟨fun h x => h (fun _ => x), fun h x => h (x 0)⟩

theorem exists_scalar_tuple (P : ℝ → Prop) :
    (∃ x : Fin 1 → ℝ, P (x 0)) ↔ ∃ x : ℝ, P x :=
  ⟨fun ⟨x, h⟩ => ⟨x 0, h⟩, fun ⟨x, h⟩ => ⟨fun _ => x, h⟩⟩

theorem realize_castLE_append_scalar {L : Language} [L.Structure ℝ]
    {α : Type*} {n q : ℕ} (ψ : L.BoundedFormula α ((n + 1) + q))
    (v : α → ℝ) (xs : Fin n → ℝ) (a : Fin 1 → ℝ) (ys : Fin q → ℝ) :
    (ψ.castLE (Nat.add_assoc n 1 q).le).Realize v
      (Fin.append xs (Fin.append a ys)) ↔
        ψ.Realize v (Fin.append (Fin.snoc xs (a 0)) ys) := by
  rw [Language.BoundedFormula.realize_castLE_of_eq (Nat.add_assoc n 1 q)]
  rw [← Fin.append_assoc, Fin.append_right_eq_snoc]

theorem isPrenex_exists_scalar_prefix {L : Language} [L.Structure ℝ]
    {α : Type*} {n : ℕ} {φ : L.BoundedFormula α n} (hφ : φ.IsPrenex) :
    ∃ blocks : QuantifierPrefix, (∀ block ∈ blocks, block.2 = 1) ∧
      ∃ ψ : L.BoundedFormula α (n + quantifierVariableCount blocks), ψ.IsQF ∧
        ∀ (v : α → ℝ) (xs : Fin n → ℝ), φ.Realize v xs ↔
          realizeQuantifierPrefix blocks (fun ys => ψ.Realize v (Fin.append xs ys)) := by
  induction hφ with
  | @of_isQF n φ hq =>
    refine ⟨[], by simp, φ, hq, ?_⟩
    intro v xs
    simp [realizeQuantifierPrefix]
  | @all n φ hp ih =>
    obtain ⟨blocks, hone, ψ, hq, hsem⟩ := ih
    refine ⟨(true, 1) :: blocks, ?_,
      ψ.castLE (Nat.add_assoc n 1 (quantifierVariableCount blocks)).le, hq.castLE, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rfl
      · exact hone b hb
    · intro v xs
      rw [Language.BoundedFormula.realize_all, realizeQuantifierPrefix_forall]
      refine (forall_scalar_tuple (fun a => φ.Realize v (Fin.snoc xs a))).symm.trans ?_
      apply forall_congr'
      intro a
      refine (hsem v (Fin.snoc xs (a 0))).trans ?_
      apply realizeQuantifierPrefix_congr
      intro ys
      exact (realize_castLE_append_scalar ψ v xs a ys).symm
  | @ex n φ hp ih =>
    obtain ⟨blocks, hone, ψ, hq, hsem⟩ := ih
    refine ⟨(false, 1) :: blocks, ?_,
      ψ.castLE (Nat.add_assoc n 1 (quantifierVariableCount blocks)).le, hq.castLE, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rfl
      · exact hone b hb
    · intro v xs
      rw [Language.BoundedFormula.realize_ex, realizeQuantifierPrefix_exists]
      refine (exists_scalar_tuple (fun a => φ.Realize v (Fin.snoc xs a))).symm.trans ?_
      apply exists_congr
      intro a
      refine (hsem v (Fin.snoc xs (a 0))).trans ?_
      apply realizeQuantifierPrefix_congr
      intro ys
      exact (realize_castLE_append_scalar ψ v xs a ys).symm

theorem rawBoundedFormula_exists_scalar_prenex {L : Language} [L.Structure ℝ]
    {α : Type*} {n : ℕ} (φ : L.BoundedFormula α n) :
    ∃ blocks : QuantifierPrefix, (∀ block ∈ blocks, block.2 = 1) ∧
      ∃ ψ : L.BoundedFormula α (n + quantifierVariableCount blocks), ψ.IsQF ∧
        ∀ (v : α → ℝ) (xs : Fin n → ℝ), φ.Realize v xs ↔
          realizeQuantifierPrefix blocks (fun ys => ψ.Realize v (Fin.append xs ys)) := by
  obtain ⟨blocks, hone, ψ, hq, hsem⟩ :=
    isPrenex_exists_scalar_prefix φ.toPrenex_isPrenex
  refine ⟨blocks, hone, ψ, hq, ?_⟩
  intro v xs
  exact φ.realize_toPrenex.symm.trans (hsem v xs)

theorem rawFormula_exists_scalar_prenex {L : Language} [L.Structure ℝ]
    {α : Type*} (φ : L.Formula α) :
    ∃ blocks : QuantifierPrefix, (∀ block ∈ blocks, block.2 = 1) ∧
      ∃ ψ : L.BoundedFormula α (quantifierVariableCount blocks), ψ.IsQF ∧
        ∀ v : α → ℝ, φ.Realize v ↔
          realizeQuantifierPrefix blocks (fun ys => ψ.Realize v ys) := by
  obtain ⟨blocks, hone, ψ, hq, hsem⟩ := rawBoundedFormula_exists_scalar_prenex φ
  refine ⟨blocks, hone, ψ.castLE (Nat.zero_add _).le, hq.castLE, ?_⟩
  intro v
  refine (hsem v Fin.elim0).trans ?_
  apply realizeQuantifierPrefix_congr
  intro ys
  rw [Language.BoundedFormula.realize_castLE_of_eq (Nat.zero_add _), Fin.elim0_append]

theorem scalar_prefix_variableCount_eq_length (blocks : QuantifierPrefix)
    (hone : ∀ block ∈ blocks, block.2 = 1) :
    quantifierVariableCount blocks = blocks.length := by
  induction blocks with
  | nil => rfl
  | cons b blocks ih =>
    have hb : b.2 = 1 := hone b (by simp)
    have ht : ∀ block ∈ blocks, block.2 = 1 := fun block h => hone block (by simp [h])
    simp [quantifierVariableCount, hb, ih ht, Nat.add_comm]

end PaperI
