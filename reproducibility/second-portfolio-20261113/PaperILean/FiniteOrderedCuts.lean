import PaperILean.CommonMonotonePartition
import PaperILean.MeasurableFirstMaximum

/-! Sorted finite unit-interval cuts with endpoint padding. Strictness is
retained exactly on active gaps, and the first endpoint index is measurable.
This module does not infer measurability of arbitrary finite-set choices. -/
noncomputable section
namespace PaperI
open Set

def PaddedUnitCutEnumeration {K : ℕ} (C : Set ℝ) (t : Fin (K+1) → ℝ) : Prop :=
  (∀ j, t j ∈ C) ∧ t 0 = 0 ∧ t (Fin.last K) = 1 ∧
    (∀ j : Fin K, t j.castSucc < t j.succ ∨ (t j.castSucc = 1 ∧ t j.succ = 1)) ∧
    ∀ c ∈ C, ∃ j, t j = c

theorem exists_paddedUnitCutEnumeration {C : Set ℝ} (hfin : C.Finite)
    (h0 : (0:ℝ) ∈ C) (h1 : (1:ℝ) ∈ C) (hC : C ⊆ Icc (0:ℝ) 1)
    (K : ℕ) (hcard : Nat.card C ≤ K+1) :
    ∃ t : Fin (K+1) → ℝ, PaddedUnitCutEnumeration C t := by
  classical
  let F := hfin.toFinset
  have hF0 : (0:ℝ) ∈ F := hfin.mem_toFinset.mpr h0
  have hF1 : (1:ℝ) ∈ F := hfin.mem_toFinset.mpr h1
  have hpos : 0 < F.card := Finset.card_pos.mpr ⟨0,hF0⟩
  have hbound : F.card ≤ K+1 := by simpa only [Nat.card_eq_card_finite_toFinset hfin] using hcard
  let n := F.card-1
  have hn : n+1 = F.card := Nat.sub_add_cancel hpos
  have hnlt : n < F.card := by omega
  let e : Fin F.card ↪o ℝ := F.orderEmbOfFin rfl
  let t : Fin (K+1) → ℝ := fun j => e ⟨min j.val n,(min_le_right _ _).trans_lt hnlt⟩
  have he_mem (j : Fin F.card) : e j ∈ C :=
    hfin.mem_toFinset.mp (F.orderEmbOfFin_mem rfl j)
  have he_surj (c : ℝ) (hc : c ∈ C) : ∃ j : Fin F.card, e j = c := by
    have : c ∈ Set.range (F.orderEmbOfFin rfl) := by
      rw [F.range_orderEmbOfFin rfl]
      exact hfin.mem_toFinset.mpr hc
    exact this
  have he0 : e ⟨0,hpos⟩ = 0 := by
    apply le_antisymm
    · obtain ⟨j,hj⟩ := he_surj 0 h0
      rw [← hj]
      exact e.monotone (show (0:ℕ) ≤ j.val from Nat.zero_le _)
    · exact (hC (he_mem _)).1
  have hen : e ⟨n,hnlt⟩ = 1 := by
    apply le_antisymm
    · exact (hC (he_mem _)).2
    · obtain ⟨j,hj⟩ := he_surj 1 h1
      rw [← hj]
      apply e.monotone
      change j.val ≤ n
      omega
  have htail (j : Fin (K+1)) (hj : n ≤ j.val) : t j = 1 := by
    simpa only [t,min_eq_right hj] using hen
  refine ⟨t,fun j => he_mem _,?_,?_,?_,?_⟩
  · simpa only [t,Fin.val_zero,Nat.zero_min] using he0
  · apply htail
    change n ≤ K
    omega
  · intro j
    by_cases hj : j.val < n
    · left
      apply e.strictMono
      change min j.val n < min (j.val+1) n
      rw [min_eq_left hj.le,min_eq_left (by omega)]
      omega
    · right
      exact ⟨htail j.castSucc (by simpa using le_of_not_gt hj),
        htail j.succ (by change n ≤ j.val+1; omega)⟩
  · intro c hc
    obtain ⟨j,hj⟩ := he_surj c hc
    refine ⟨⟨j.val,j.isLt.trans_le hbound⟩,?_⟩
    have hjn : j.val ≤ n := by omega
    simpa only [t,min_eq_left hjn] using hj

theorem PaddedUnitCutEnumeration.monotone {K : ℕ} {C : Set ℝ}
    {t : Fin (K+1) → ℝ} (h : PaddedUnitCutEnumeration C t) : Monotone t := by
  apply Fin.monotone_iff_le_succ.mpr
  intro j
  rcases h.2.2.2.1 j with hj | ⟨hj,hj'⟩
  · exact hj.le
  · exact le_of_eq (hj.trans hj'.symm)

theorem PaddedUnitCutEnumeration.gap {K : ℕ} {C : Set ℝ}
    {t : Fin (K+1) → ℝ} (h : PaddedUnitCutEnumeration C t) (j : Fin K) :
    ∀ c ∈ C, c ∉ Ioo (t j.castSucc) (t j.succ) := by
  intro c hc hbetween
  obtain ⟨k,rfl⟩ := h.2.2.2.2 c hc
  by_cases hkj : k.val ≤ j.val
  · exact (not_lt_of_ge (h.monotone hkj)) hbetween.1
  · have hjk : j.succ ≤ k := by change j.val+1 ≤ k.val; omega
    exact (not_lt_of_ge (h.monotone hjk)) hbetween.2

def paddedCutSequence {K : ℕ} (t : Fin (K+1) → ℝ) (j : ℕ) : ℝ :=
  if h : j < K+1 then t ⟨j,h⟩ else 1

theorem paddedCutSequence_of_lt {K : ℕ} (t : Fin (K+1) → ℝ) {j : ℕ}
    (hj : j < K+1) : paddedCutSequence t j = t ⟨j,hj⟩ := by
  simp [paddedCutSequence,hj]

theorem paddedCutSequence_last {K : ℕ} (t : Fin (K+1) → ℝ)
    (ht : t (Fin.last K)=1) : paddedCutSequence t K=1 := by
  simpa only [paddedCutSequence_of_lt t (Nat.lt_succ_self K)] using ht

def activeCutCount {K : ℕ} (t : Fin (K+1) → ℝ) (ht : t (Fin.last K)=1) : ℕ :=
  Nat.find (show ∃ j, paddedCutSequence t j=1 from ⟨K,paddedCutSequence_last t ht⟩)

theorem activeCutCount_spec {K : ℕ} (t : Fin (K+1) → ℝ)
    (ht : t (Fin.last K)=1) :
    activeCutCount t ht ≤ K ∧ paddedCutSequence t (activeCutCount t ht)=1 ∧
      ∀ j < activeCutCount t ht, paddedCutSequence t j ≠ 1 := by
  have hex : ∃ j, paddedCutSequence t j=1 := ⟨K,paddedCutSequence_last t ht⟩
  exact ⟨Nat.find_min' hex (paddedCutSequence_last t ht),Nat.find_spec hex,
    fun j hj => Nat.find_min hex hj⟩

theorem PaddedUnitCutEnumeration.active_partition {K : ℕ} {C : Set ℝ}
    {t : Fin (K+1) → ℝ} (h : PaddedUnitCutEnumeration C t)
    (hC : C ⊆ Icc (0:ℝ) 1) :
    let n := activeCutCount t h.2.2.1
    let s := paddedCutSequence t
    0<n ∧ n≤K ∧ s 0=0 ∧ s n=1 ∧ MonotoneOn s (Icc 0 n) ∧
      (∀ j≥n, s j=1) ∧
      ∀ j<n, s j ∈ C ∧ s (j+1) ∈ C ∧ s j<s (j+1) ∧
        ∀ c ∈ C, c ∉ Ioo (s j) (s (j+1)) := by
  dsimp only
  let n := activeCutCount t h.2.2.1
  have hn : n ≤ K ∧ paddedCutSequence t n=1 ∧
      ∀ j<n, paddedCutSequence t j ≠ 1 := activeCutCount_spec t h.2.2.1
  have hs0 : paddedCutSequence t 0=0 := by
    simpa only [paddedCutSequence_of_lt t (Nat.zero_lt_succ K)] using h.2.1
  have hnp : 0<n := by
    by_contra hnot
    have hz : n=0 := by omega
    have hh := hn.2.1
    change paddedCutSequence t n=1 at hh
    rw [hz,hs0] at hh
    norm_num at hh
  refine ⟨hnp,hn.1,hs0,hn.2.1,?_,?_,?_⟩
  · intro i hi j hj hij
    have hi' : i≤n := hi.2
    have hj' : j≤n := hj.2
    rw [paddedCutSequence_of_lt t (by omega),paddedCutSequence_of_lt t (by omega)]
    exact h.monotone hij
  · intro j hj
    by_cases hjK : j<K+1
    · rw [paddedCutSequence_of_lt t hjK]
      apply le_antisymm (hC (h.1 _)).2
      have hle := h.monotone (show (⟨n,by omega⟩ : Fin (K+1)) ≤ ⟨j,hjK⟩ from hj)
      have hnval : t ⟨n,by omega⟩=1 := by
        simpa only [paddedCutSequence_of_lt t (show n<K+1 by omega)] using hn.2.1
      simpa only [hnval] using hle
    · simp [paddedCutSequence,hjK]
  · intro j hj
    have hjK : j<K := by omega
    have hj0 : j<K+1 := by omega
    have hj1 : j+1<K+1 := by omega
    rw [paddedCutSequence_of_lt t hj0,paddedCutSequence_of_lt t hj1]
    refine ⟨h.1 _,h.1 _,?_,h.gap ⟨j,hjK⟩⟩
    rcases h.2.2.2.1 ⟨j,hjK⟩ with hlt | ⟨he,_⟩
    · exact hlt
    · exact (hn.2.2 j hj ((paddedCutSequence_of_lt t hj0).trans he)).elim

theorem measurable_paddedCutSequence {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (t : Ω → Fin (K+1) → ℝ) (ht : Measurable t) (j : ℕ) :
    Measurable (fun ω => paddedCutSequence (t ω) j) := by
  by_cases hj : j<K+1
  · simpa only [paddedCutSequence_of_lt _ hj] using (measurable_pi_apply ⟨j,hj⟩).comp ht
  · simpa only [paddedCutSequence,dif_neg hj] using (measurable_const (a := (1:ℝ)))

theorem measurable_activeCutCount {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (t : Ω → Fin (K+1) → ℝ) (ht : Measurable t)
    (hlast : ∀ ω, t ω (Fin.last K)=1) :
    Measurable (fun ω => activeCutCount (t ω) (hlast ω)) :=
  measurable_find (fun ω => ⟨K,paddedCutSequence_last (t ω) (hlast ω)⟩)
    (fun j => measurableSet_eq_fun (measurable_paddedCutSequence t ht j) measurable_const)

end PaperI
