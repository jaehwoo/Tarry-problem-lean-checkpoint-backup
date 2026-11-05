import PaperILean.MainStatement
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-! Stars-and-bars cardinality for the complete coefficient index. -/

open scoped BigOperators

noncomputable section
namespace PaperI

def NaturalDegreeLE (k : ℕ) := {α : Fin 3 → ℕ // ∑ i, α i ≤ k}

def slackExponentEquiv (k : ℕ) :
    NaturalDegreeLE k ≃ {β : Fin 4 → ℕ // ∑ i, β i = k} where
  toFun α := ⟨Fin.cons (k - ∑ i, α.val i) α.val, by
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using
      Nat.sub_add_cancel α.property⟩
  invFun β := ⟨Fin.tail β.val, by
    have h : β.val 0 + ∑ i : Fin 3, β.val i.succ = k := by
      simpa only [Fin.sum_univ_succ] using β.property
    change (∑ i : Fin 3, β.val i.succ) ≤ k
    omega⟩
  left_inv α := by
    apply Subtype.ext
    funext i
    rfl
  right_inv β := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h : β.val 0 + ∑ j : Fin 3, β.val j.succ = k := by
        simpa only [Fin.sum_univ_succ] using β.property
      change k - (∑ j : Fin 3, β.val j.succ) = β.val 0
      omega
    · rfl

def naturalDegreeLESymEquiv (k : ℕ) : NaturalDegreeLE k ≃ Sym (Fin 4) k :=
  (slackExponentEquiv k).trans (Sym.equivNatSumOfFintype (Fin 4) k).symm

instance (k : ℕ) : Fintype (NaturalDegreeLE k) :=
  Fintype.ofEquiv (Sym (Fin 4) k) (naturalDegreeLESymEquiv k).symm

theorem card_naturalDegreeLE (k : ℕ) : Fintype.card (NaturalDegreeLE k) = (k + 3).choose 3 := by
  rw [Fintype.card_congr (naturalDegreeLESymEquiv k), Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have h : 4 + k - 1 = k + 3 := by omega
  rw [h]
  exact Nat.choose_symm_of_eq_add (by omega)

theorem naturalExponent_le_sum (α : Fin 3 → ℕ) (i : Fin 3) : α i ≤ ∑ j, α j :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

def positiveNaturalIndexEquiv (k : ℕ) :
    MonomialIndex k ≃ {α : NaturalDegreeLE k // α.val ≠ 0} where
  toFun α := ⟨⟨fun i => (α.val i).val, α.property.2⟩, by
    intro h
    change (fun i : Fin 3 => (α.val i).val) = 0 at h
    have hz : ∑ i : Fin 3, (α.val i).val = 0 := by
      simp only [h, Pi.zero_apply, Finset.sum_const_zero]
    have hp := α.property.1
    change 1 ≤ ∑ i : Fin 3, (α.val i).val at hp
    omega⟩
  invFun α := ⟨fun i => ⟨α.val.val i,
      Nat.lt_succ_of_le ((naturalExponent_le_sum α.val.val i).trans α.val.property)⟩, by
    refine ⟨?_, α.val.property⟩
    change 1 ≤ ∑ i : Fin 3, α.val.val i
    apply Nat.one_le_iff_ne_zero.mpr
    intro h
    apply α.property
    funext i
    exact Nat.eq_zero_of_le_zero (h ▸ naturalExponent_le_sum α.val.val i)⟩
  left_inv α := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
  right_inv α := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

def zeroNaturalIndexEquiv (k : ℕ) :
    {α : NaturalDegreeLE k // α.val = 0} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨⟨0, by simp⟩, rfl⟩
  left_inv α := by
    apply Subtype.ext
    apply Subtype.ext
    exact α.property.symm
  right_inv u := by cases u; rfl

theorem card_monomialIndex (k : ℕ) : Fintype.card (MonomialIndex k) = dimension k := by
  classical
  rw [Fintype.card_congr (positiveNaturalIndexEquiv k),
    Fintype.card_subtype_compl (fun α : NaturalDegreeLE k => α.val = 0),
    card_naturalDegreeLE, Fintype.card_congr (zeroNaturalIndexEquiv k)]
  simp [dimension]

end PaperI
