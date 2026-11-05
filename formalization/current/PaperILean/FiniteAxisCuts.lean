import PaperILean.UniformScalarFrontier
import Mathlib.Analysis.Convex.Topology

/-! Whole-axis open cells and singleton cuts. Empty cell labels are permitted;
the conservative powerset count is uniform and avoids any separation premise. -/
noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable

def axisCutCell (C L : Finset ℝ) : Set ℝ :=
  ⋂ c ∈ C, if c ∈ L then Ioi c else Iio c

theorem mem_axisCutCell (C L : Finset ℝ) (t : ℝ) :
    t ∈ axisCutCell C L ↔ ∀ c ∈ C, if c ∈ L then c < t else t < c := by
  simp only [axisCutCell, mem_iInter]
  congr! 2
  split <;> rfl

theorem axisCutCell_open (C L : Finset ℝ) : IsOpen (axisCutCell C L) := by
  apply isOpen_biInter_finset
  intro c hc
  split <;> first | exact isOpen_Ioi | exact isOpen_Iio

theorem axisCutCell_preconnected (C L : Finset ℝ) : IsPreconnected (axisCutCell C L) := by
  apply (show Convex ℝ (axisCutCell C L) from ?_).isPreconnected
  apply convex_iInter
  intro c
  apply convex_iInter
  intro hc
  split <;> first | exact convex_Ioi c | exact convex_Iio c

theorem axisCutCell_avoids (C L : Finset ℝ) {t : ℝ}
    (ht : t ∈ axisCutCell C L) : t ∉ C := by
  intro h
  have hlt := (mem_axisCutCell C L t).mp ht t h
  split at hlt <;> exact (lt_irrefl t hlt)

theorem axisCutCell_cover (C : Finset ℝ) {t : ℝ} (ht : t ∉ C) :
    ∃ L ∈ C.powerset, t ∈ axisCutCell C L := by
  classical
  refine ⟨C.filter (· < t), Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
  rw [mem_axisCutCell]
  intro c hc
  simp only [Finset.mem_filter, hc, true_and]
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (le_of_not_gt h) (by intro he; exact ht (he ▸ hc))

theorem axisCutCell_disjoint (C L M : Finset ℝ) (hL : L ⊆ C) (hM : M ⊆ C)
    (hne : L ≠ M) : Disjoint (axisCutCell C L) (axisCutCell C M) := by
  classical
  apply Set.disjoint_left.mpr
  intro t ht hu
  apply hne
  apply Finset.ext
  intro c
  by_cases hc : c ∈ C
  · have hl := (mem_axisCutCell C L t).mp ht c hc
    have hm := (mem_axisCutCell C M t).mp hu c hc
    by_cases hcl : c ∈ L <;> by_cases hcm : c ∈ M <;> simp_all <;> linarith
  · simp only [show c ∉ L from fun h => hc (hL h), show c ∉ M from fun h => hc (hM h)]

/-- A cell in any coordinate space is described by the actual linear cut tests. -/
theorem axisCutCell_format {α : Type*} (a : α) (C L : Finset ℝ) :
    HasBoundedSignFormat C.card 1 {x : α → ℝ | x a ∈ axisCutCell C L} := by
  classical
  let q : ℝ → MvPolynomial α ℝ := fun c => MvPolynomial.X a - MvPolynomial.C c
  refine ⟨C.image q, Finset.card_image_le, ?_, ?_⟩
  · intro p hp
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hp
    exact (MvPolynomial.totalDegree_sub _ _).trans (by simp [q])
  · intro x y hxy
    change x a ∈ axisCutCell C L ↔ y a ∈ axisCutCell C L
    rw [mem_axisCutCell, mem_axisCutCell]
    apply forall_congr'
    intro c
    apply forall_congr'
    intro hc
    have hs := hxy (q c) (Finset.mem_image.mpr ⟨c,hc,rfl⟩)
    have hpos : c < x a ↔ c < y a := by
      simpa only [q, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_pos] using hs.2
    have hnonneg : c ≤ x a ↔ c ≤ y a := by
      simpa only [q, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_nonneg] using
        realSignEquivalent_nonneg hs
    split_ifs
    · exact hpos
    · exact not_le.symm.trans ((not_congr hnonneg).trans not_le)

theorem HasBoundedSignFormat.inter {α : Type*} {s d s' d' : ℕ}
    {S T : Set (α → ℝ)} (hS : HasBoundedSignFormat s d S)
    (hT : HasBoundedSignFormat s' d' T) :
    HasBoundedSignFormat (s+s') (max d d') (S ∩ T) := by
  classical
  obtain ⟨A,hc,hd,hA⟩ := hS
  obtain ⟨B,hcB,hdB,hB⟩ := hT
  refine ⟨A ∪ B, (Finset.card_union_le A B).trans (Nat.add_le_add hc hcB), ?_,
    polynomialSignDetermined_inter hA hB⟩
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · exact (hd q hq).trans (le_max_left _ _)
  · exact (hdB q hq).trans (le_max_right _ _)

end PaperI
