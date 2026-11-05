import PaperILean.IndexCombinatorics

/-! All-degree combinatorial weight of one monomial coordinate. This counts
the diagonal character exponent; it does not by itself prove the determinant
for general affine frames. -/

open scoped BigOperators

noncomputable section
namespace PaperI

def DegreeBoundedIndex (d k : ℕ) := {α : Fin d → ℕ // ∑ i, α i ≤ k}

def degreeSlackEquiv (d k : ℕ) :
    DegreeBoundedIndex d k ≃ {β : Fin (d + 1) → ℕ // ∑ i, β i = k} where
  toFun α := ⟨Fin.cons (k - ∑ i, α.val i) α.val, by
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using
      Nat.sub_add_cancel α.property⟩
  invFun β := ⟨Fin.tail β.val, by
    have h : β.val 0 + ∑ i : Fin d, β.val i.succ = k := by
      simpa only [Fin.sum_univ_succ] using β.property
    change (∑ i : Fin d, β.val i.succ) ≤ k
    omega⟩
  left_inv α := by
    apply Subtype.ext
    funext i
    rfl
  right_inv β := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h : β.val 0 + ∑ j : Fin d, β.val j.succ = k := by
        simpa only [Fin.sum_univ_succ] using β.property
      change k - (∑ j : Fin d, β.val j.succ) = β.val 0
      omega
    · rfl

def degreeBoundedSymEquiv (d k : ℕ) : DegreeBoundedIndex d k ≃ Sym (Fin (d + 1)) k :=
  (degreeSlackEquiv d k).trans (Sym.equivNatSumOfFintype (Fin (d + 1)) k).symm

instance (d k : ℕ) : Fintype (DegreeBoundedIndex d k) :=
  Fintype.ofEquiv (Sym (Fin (d + 1)) k) (degreeBoundedSymEquiv d k).symm

theorem card_degreeBoundedIndex (d k : ℕ) :
    Fintype.card (DegreeBoundedIndex d k) = (k + d).choose d := by
  rw [Fintype.card_congr (degreeBoundedSymEquiv d k), Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have h : d + 1 + k - 1 = k + d := by omega
  rw [h]
  exact Nat.choose_symm_of_eq_add (by omega)

def markedExponentEquiv (d k : ℕ) :
    (Σ α : DegreeBoundedIndex (d + 1) (k + 1), Fin (α.val 0)) ≃
      DegreeBoundedIndex (d + 2) k where
  toFun z := ⟨Fin.cons z.2.val (Fin.cons (z.1.val 0 - z.2.val - 1) (Fin.tail z.1.val)), by
    have h := z.1.property
    rw [Fin.sum_univ_succ] at h
    have hj := z.2.isLt
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    change z.2.val + (z.1.val 0 - z.2.val - 1 +
      ∑ i : Fin d, z.1.val i.succ) ≤ k
    omega⟩
  invFun β := ⟨⟨Fin.cons (β.val 0 + β.val (0 : Fin (d + 1)).succ + 1)
      (Fin.tail (Fin.tail β.val)), by
        have h := β.property
        simp only [Fin.sum_univ_succ] at h
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        change β.val 0 + β.val (0 : Fin (d + 1)).succ + 1 +
          (∑ i : Fin d, β.val i.succ.succ) ≤ k + 1
        omega⟩,
    ⟨β.val 0, by
      change β.val 0 < β.val 0 + β.val (0 : Fin (d + 1)).succ + 1
      omega⟩⟩
  left_inv z := by
    have hval : (Fin.cons (z.2.val + (z.1.val 0 - z.2.val - 1) + 1)
        (Fin.tail z.1.val) : Fin (d + 1) → ℕ) = z.1.val := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change z.2.val + (z.1.val 0 - z.2.val - 1) + 1 = z.1.val 0
        have hj := z.2.isLt
        omega
      · rfl
    apply Sigma.ext
    · exact Subtype.ext hval
    · exact (Fin.heq_ext_iff (congrFun hval 0)).mpr rfl
  right_inv β := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · change β.val 0 + β.val (0 : Fin (d + 1)).succ + 1 - β.val 0 - 1 =
          β.val (0 : Fin (d + 1)).succ
        omega
      · rfl

theorem sum_firstExponent (d k : ℕ) :
    (∑ α : DegreeBoundedIndex (d + 1) k, α.val 0) =
      (k + d + 1).choose (d + 2) := by
  classical
  cases k with
  | zero =>
    have hz : ∀ α : DegreeBoundedIndex (d + 1) 0, α.val 0 = 0 := by
      intro α
      have h := Finset.single_le_sum (f := α.val) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ (0 : Fin (d + 1)))
      exact Nat.eq_zero_of_le_zero (h.trans α.property)
    simp only [hz, Finset.sum_const_zero, zero_add]
    exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ k =>
    have hcard := Fintype.card_congr (markedExponentEquiv d k)
    rw [Fintype.card_sigma, card_degreeBoundedIndex] at hcard
    simp only [Fintype.card_fin] at hcard
    convert hcard using 1
    congr 1
    omega

def degreePermutationEquiv (d k : ℕ) (e : Fin d ≃ Fin d) :
    DegreeBoundedIndex d k ≃ DegreeBoundedIndex d k where
  toFun α := ⟨fun i => α.val (e i), by
    calc
      (∑ i, α.val (e i)) = ∑ i, α.val i := e.sum_comp α.val
      _ ≤ k := α.property⟩
  invFun α := ⟨fun i => α.val (e.symm i), by
    calc
      (∑ i, α.val (e.symm i)) = ∑ i, α.val i := e.symm.sum_comp α.val
      _ ≤ k := α.property⟩
  left_inv α := by
    apply Subtype.ext
    funext i
    simp
  right_inv α := by
    apply Subtype.ext
    funext i
    simp

theorem sum_coordinateExponent (d k : ℕ) (i : Fin (d + 1)) :
    (∑ α : DegreeBoundedIndex (d + 1) k, α.val i) =
      (k + d + 1).choose (d + 2) := by
  classical
  have h := (degreePermutationEquiv (d + 1) k (Equiv.swap 0 i)).sum_comp
    (fun α : DegreeBoundedIndex (d + 1) k => α.val 0)
  have hs : (∑ α : DegreeBoundedIndex (d + 1) k, α.val i) =
      ∑ α : DegreeBoundedIndex (d + 1) k, α.val 0 := by
    simpa only [degreePermutationEquiv, Equiv.coe_fn_mk, Equiv.swap_apply_left] using h
  rw [hs, sum_firstExponent]

theorem sum_monomialCoordinate (k : ℕ) (i : Fin 3) :
    (∑ α : MonomialIndex k, (α.val i).val) = chi k := by
  classical
  have hz : (∑ α : {α : NaturalDegreeLE k // α.val = 0}, α.val.val i) = 0 := by
    apply Finset.sum_eq_zero
    intro α hα
    rw [α.property]
    rfl
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun α : NaturalDegreeLE k => α.val = 0) (fun α => α.val i)
  rw [hz, zero_add] at hsplit
  have he := (positiveNaturalIndexEquiv k).sum_comp
    (fun α : {α : NaturalDegreeLE k // α.val ≠ 0} => α.val.val i)
  change (∑ α : MonomialIndex k, (α.val i).val) =
    ∑ α : {α : NaturalDegreeLE k // α.val ≠ 0}, α.val.val i at he
  rw [he, hsplit]
  exact sum_coordinateExponent 2 k i

end PaperI
