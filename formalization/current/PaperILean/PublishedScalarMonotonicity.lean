import PaperILean.MonotonicityBadSet
import PaperILean.PolynomialSignDescription

/-! Accepted qualitative one-variable monotonicity, specialized from Ta Le Loi,
Lecture 1: O-minimal structures, Theorem 2.6 (printed page 22), with the real
algebraic structure of Example 1.4. The input yields finite strict/constant
cells only: it supplies no uniform count, path construction or analytic format.
The local proofs identify the actual bad locus as a finite subset of those cuts. -/

noncomputable section
namespace PaperI
open Set

/-- The actual scalar graph on the open interval, in two real coordinates. -/
def openScalarGraph (f : ℝ → ℝ) (a b : ℝ) : Set (Fin 2 → ℝ) :=
  {v | a < v 0 ∧ v 0 < b ∧ v 1 = f (v 0)}

/-- The three alternatives in the qualitative monotonicity theorem. -/
def StrictMonotoneOnCutIntervals (f : ℝ → ℝ) (C : Finset ℝ) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
    StrictMonoOn f (Ioo u v) ∨ StrictAntiOn f (Ioo u v) ∨
      ∃ z : ℝ, ∀ s ∈ Ioo u v, f s = z

/-- Explicit accepted published input. This qualitative finite subdivision has no
format-uniform bound. No inhabitant of this structure is supplied. -/
structure PublishedOneVariableMonotonicity : Prop where
  finite_strict_subdivision : ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    HasPolynomialSignDescription (openScalarGraph f a b) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        StrictMonotoneOnCutIntervals f C

/-- An interior point outside the cuts lies strictly between consecutive cuts. -/
theorem exists_consecutive_cuts_around_point (C : Finset ℝ) {a b x : ℝ}
    (ha : a ∈ C) (hb : b ∈ C) (hx : x ∈ Ioo a b) (hxc : x ∉ C) :
    ∃ l ∈ C, ∃ r ∈ C, l < x ∧ x < r ∧ ∀ c ∈ C, c ∉ Ioo l r := by
  classical
  let L := C.filter (fun c => c ≤ x)
  let R := C.filter (fun c => x ≤ c)
  have hL : L.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, hx.1.le⟩⟩
  have hR : R.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hx.2.le⟩⟩
  let l := L.max' hL
  let r := R.min' hR
  have hl : l ∈ C ∧ l ≤ x := Finset.mem_filter.mp (L.max'_mem hL)
  have hr : r ∈ C ∧ x ≤ r := Finset.mem_filter.mp (R.min'_mem hR)
  have hlx : l < x := lt_of_le_of_ne hl.2 (fun h => hxc (h ▸ hl.1))
  have hxr : x < r := lt_of_le_of_ne hr.2 (fun h => hxc (h.symm ▸ hr.1))
  refine ⟨l, hl.1, r, hr.1, hlx, hxr, ?_⟩
  intro c hc hcr
  by_cases hcx : c ≤ x
  · have hcl : c ≤ l := L.le_max' c (Finset.mem_filter.mpr ⟨hc, hcx⟩)
    exact (not_lt_of_ge hcl) hcr.1
  · have hrc : r ≤ c := R.min'_le c (Finset.mem_filter.mpr ⟨hc, (lt_of_not_ge hcx).le⟩)
    exact (not_lt_of_ge hrc) hcr.2

theorem monotonicityBadSet_subset_of_strict_cut_intervals
    (f : ℝ → ℝ) (C : Finset ℝ) {a b : ℝ}
    (ha : a ∈ C) (hb : b ∈ C) (hC : ∀ c ∈ C, c ∈ Icc a b)
    (hf : StrictMonotoneOnCutIntervals f C) :
    MonotonicityBadSet f a b ⊆ (C : Set ℝ) := by
  classical
  intro x hx
  by_contra hxc
  obtain ⟨l, hl, r, hr, hlx, hxr, hgap⟩ :=
    exists_consecutive_cuts_around_point C ha hb hx.1 hxc
  apply hx.2
  refine ⟨l, r, (hC l hl).1, (hC r hr).2, hlx, hxr, ?_⟩
  rcases hf l hl r hr (hlx.trans hxr) hgap with hm | ha | ⟨z, hz⟩
  · exact Or.inl hm
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (fun s hs => (hz s hs).trans (hz x ⟨hlx, hxr⟩).symm))

/-- The finite bad set is a locally proved consequence of qualitative published
monotonicity. Degenerate and reversed intervals require no external input. -/
theorem published_monotonicityBadSet_finite (hMono : PublishedOneVariableMonotonicity)
    (f : ℝ → ℝ) (a b : ℝ)
    (hGraph : HasPolynomialSignDescription (openScalarGraph f a b)) :
    (MonotonicityBadSet f a b).Finite := by
  by_cases hab : a < b
  · obtain ⟨C, ha, hb, hC, hf⟩ := hMono.finite_strict_subdivision f a b hab hGraph
    exact C.finite_toSet.subset
      (monotonicityBadSet_subset_of_strict_cut_intervals f C ha hb hC hf)
  · apply Set.finite_empty.subset
    intro x hx
    exact (hab (hx.1.1.trans hx.1.2)).elim

end PaperI
