import PaperILean.AllDimCoefficientSpace
import PaperILean.CharacterCombinatorics

/-! Cardinality and total coordinate weights of the unchanged complete index.
The weight proof counts all degrees at once. It is an alternative to the
manuscript's homogeneous permutation-symmetry and hockey-stick argument. -/

open scoped BigOperators
noncomputable section
namespace PaperI.AllDim
variable {n : ℕ}

theorem naturalExponent_le_sum (α : Fin n → ℕ) (i : Fin n) : α i ≤ ∑ j, α j :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

def positiveNaturalIndexEquiv (n k : ℕ) :
    MonomialIndex n k ≃ {α : PaperI.DegreeBoundedIndex n k // α.val ≠ 0} where
  toFun α := ⟨⟨fun i => (α.val i).val, α.property.2⟩, by
    intro h
    change (fun i : Fin n => (α.val i).val) = 0 at h
    have hz : ∑ i : Fin n, (α.val i).val = 0 := by
      simp only [h, Pi.zero_apply, Finset.sum_const_zero]
    have hp := α.property.1
    change 1 ≤ ∑ i : Fin n, (α.val i).val at hp
    omega⟩
  invFun α := ⟨fun i => ⟨α.val.val i,
      Nat.lt_succ_of_le ((naturalExponent_le_sum α.val.val i).trans α.val.property)⟩, by
    refine ⟨?_, α.val.property⟩
    change 1 ≤ ∑ i : Fin n, α.val.val i
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

def zeroNaturalIndexEquiv (n k : ℕ) :
    {α : PaperI.DegreeBoundedIndex n k // α.val = 0} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨⟨0, by simp⟩, rfl⟩
  left_inv α := by
    apply Subtype.ext
    apply Subtype.ext
    exact α.property.symm
  right_inv u := by cases u; rfl

theorem card_monomialIndex (n k : ℕ) : Fintype.card (MonomialIndex n k) = dimension n k := by
  classical
  rw [Fintype.card_congr (positiveNaturalIndexEquiv n k),
    Fintype.card_subtype_compl (fun α : PaperI.DegreeBoundedIndex n k => α.val = 0),
    PaperI.card_degreeBoundedIndex, Fintype.card_congr (zeroNaturalIndexEquiv n k)]
  simp [dimension]


theorem sum_monomialCoordinate (n k : ℕ) (i : Fin n) :
    (∑ α : MonomialIndex n k, (α.val i).val) = chi n k := by
  classical
  have hz : (∑ α : {α : PaperI.DegreeBoundedIndex n k // α.val = 0}, α.val.val i) = 0 := by
    apply Finset.sum_eq_zero
    intro α hα
    rw [α.property]
    rfl
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun α : PaperI.DegreeBoundedIndex n k => α.val = 0) (fun α => α.val i)
  rw [hz, zero_add] at hsplit
  have he := (positiveNaturalIndexEquiv n k).sum_comp
    (fun α : {α : PaperI.DegreeBoundedIndex n k // α.val ≠ 0} => α.val.val i)
  change (∑ α : MonomialIndex n k, (α.val i).val) =
    ∑ α : {α : PaperI.DegreeBoundedIndex n k // α.val ≠ 0}, α.val.val i at he
  rw [he, hsplit]
  cases n with
  | zero => exact Fin.elim0 i
  | succ d => simpa [chi, Nat.add_assoc] using PaperI.sum_coordinateExponent d k i

end PaperI.AllDim
