import PaperILean.DerivativeSignSubdivision
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Endpoint-safe calculus on the actual finite analytic/sign subdivision.
No derivative or body continuity is required at any cut. -/
noncomputable section
namespace PaperI.FinitePieceFTC
open Set MeasureTheory

/-- FTC across a finite exceptional set. Continuity is retained at every cut. -/
theorem integral_eq_sub_off_finset (C : Finset ℝ) (f f' : ℝ → ℝ)
    (a z : ℝ) (haz : a ≤ z) (hc : ContinuousOn f (Icc a z))
    (hi : IntervalIntegrable f' volume a z)
    (hd : ∀ t ∈ Ioo a z, t ∉ C → HasDerivAt f (f' t) t) :
    (∫ t in a..z, f' t) = f z - f a := by
  classical
  induction C using Finset.induction_on generalizing a z with
  | empty =>
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le haz hc
      (fun t ht => hd t ht (by simp)) hi
  | @insert c C hnot ih =>
    by_cases hcin : c ∈ Ioo a z
    · have hl : Icc a c ⊆ Icc a z := Icc_subset_Icc le_rfl hcin.2.le
      have hr : Icc c z ⊆ Icc a z := Icc_subset_Icc hcin.1.le le_rfl
      have hil : IntervalIntegrable f' volume a c := hi.mono_set (by
        simpa only [uIcc_of_le haz,uIcc_of_le hcin.1.le] using hl)
      have hir : IntervalIntegrable f' volume c z := hi.mono_set (by
        simpa only [uIcc_of_le haz,uIcc_of_le hcin.2.le] using hr)
      have hleft := ih a c hcin.1.le (hc.mono hl) hil (by
        intro t ht htC
        exact hd t ⟨ht.1,ht.2.trans hcin.2⟩
          (by simp only [Finset.mem_insert,not_or]; exact ⟨ne_of_lt ht.2,htC⟩))
      have hright := ih c z hcin.2.le (hc.mono hr) hir (by
        intro t ht htC
        exact hd t ⟨hcin.1.trans ht.1,ht.2⟩
          (by simp only [Finset.mem_insert,not_or]; exact ⟨ne_of_gt ht.1,htC⟩))
      rw [← intervalIntegral.integral_add_adjacent_intervals hil hir,hleft,hright]
      ring
    · apply ih a z haz hc hi
      intro t ht htC
      apply hd t ht
      simp only [Finset.mem_insert,not_or]
      exact ⟨fun h => hcin (h ▸ ht),htC⟩

/-- A point outside the cuts lies in a genuine consecutive open gap. -/
theorem point_in_cut_gap (C : Finset ℝ) {a z t : ℝ}
    (ha : a ∈ C) (hz : z ∈ C) (ht : t ∈ Ioo a z) (htC : t ∉ C) :
    ∃ u ∈ C, ∃ v ∈ C, u < v ∧ t ∈ Ioo u v ∧
      ∀ c ∈ C, c ∉ Ioo u v := by
  classical
  let L := C.filter (fun c => c ≤ t)
  let R := C.filter (fun c => t ≤ c)
  have hL : L.Nonempty := ⟨a,Finset.mem_filter.mpr ⟨ha,ht.1.le⟩⟩
  have hR : R.Nonempty := ⟨z,Finset.mem_filter.mpr ⟨hz,ht.2.le⟩⟩
  let u := L.max' hL
  let v := R.min' hR
  have hu : u ∈ C ∧ u ≤ t := Finset.mem_filter.mp (L.max'_mem hL)
  have hv : v ∈ C ∧ t ≤ v := Finset.mem_filter.mp (R.min'_mem hR)
  have hut : u < t := lt_of_le_of_ne hu.2 (fun h => htC (h ▸ hu.1))
  have htv : t < v := lt_of_le_of_ne hv.2 (fun h => htC (h.symm ▸ hv.1))
  refine ⟨u,hu.1,v,hv.1,hut.trans htv,⟨hut,htv⟩,?_⟩
  intro c hc hcv
  by_cases hct : c ≤ t
  · have hcu : c ≤ u := L.le_max' c (Finset.mem_filter.mpr ⟨hc,hct⟩)
    exact (not_lt_of_ge hcu) hcv.1
  · have hvc : v ≤ c := R.min'_le c (Finset.mem_filter.mpr ⟨hc,(lt_of_not_ge hct).le⟩)
    exact (not_lt_of_ge hvc) hcv.2

/-- The sign is imposed on the actual derivative, and endpoint derivatives
may be singular. Automatic integrability follows from scalar FTC. -/
theorem signed_derivative_integrable (q q' : ℝ → ℝ) (a z : ℝ)
    (haz : a ≤ z) (hc : ContinuousOn q (Icc a z))
    (hd : ∀ t ∈ Ioo a z, HasDerivAt q (q' t) t)
    (hs : DerivativeSignOn q (Ioo a z)) :
    IntervalIntegrable q' volume a z := by
  have hsign : (∀ t ∈ Ioo a z, 0 ≤ q' t) ∨ (∀ t ∈ Ioo a z, q' t ≤ 0) := by
    rcases hs with hp | hn | hz
    · exact Or.inl (fun t ht => by rw [← (hd t ht).deriv]; exact (hp t ht).le)
    · exact Or.inr (fun t ht => by rw [← (hd t ht).deriv]; exact (hn t ht).le)
    · exact Or.inl (fun t ht => by rw [← (hd t ht).deriv,hz t ht])
  rcases hsign with hp | hn
  · exact intervalIntegral.intervalIntegrable_deriv_of_nonneg
      (by simpa only [uIcc_of_le haz] using hc)
      (by simpa only [min_eq_left haz,max_eq_right haz] using hd)
      (by simpa only [min_eq_left haz,max_eq_right haz] using hp)
  · have hi : IntervalIntegrable (fun t => -q' t) volume a z :=
      intervalIntegral.intervalIntegrable_deriv_of_nonneg
        (g := fun t => -q t)
        (by simpa only [uIcc_of_le haz] using hc.neg)
        (by simpa only [min_eq_left haz,max_eq_right haz] using fun t ht => (hd t ht).neg)
        (by simpa only [min_eq_left haz,max_eq_right haz] using
          fun t ht => neg_nonneg.mpr (hn t ht))
    have hneg := hi.neg
    change IntervalIntegrable (fun t => -(-q' t)) volume a z at hneg
    simpa only [neg_neg] using hneg

/-- Glue the actual derivative integrals over the finite subdivision. -/
theorem derivative_integrable_on_cut_pieces (q q' : ℝ → ℝ)
    (C : Finset ℝ) (a z : ℝ) (ha : a ∈ C) (hz : z ∈ C)
    (hC : ∀ c ∈ C, c ∈ Icc a z) (hc : ContinuousOn q (Icc a z))
    (hp : ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
      (∀ t ∈ Ioo u v, HasDerivAt q (q' t) t) ∧ DerivativeSignOn q (Ioo u v)) :
    IntervalIntegrable q' volume a z := by
  obtain ⟨n,t,_hn,ht0,htn,_ht,hgap⟩ := exists_sorted_cut_partition C ha hz hC
  have hi (j : ℕ) (hj : j<n) : IntervalIntegrable q' volume (t j) (t (j+1)) := by
    obtain ⟨hu,hv,huv,hno⟩ := hgap j hj
    obtain ⟨hd,hs⟩ := hp (t j) hu (t (j+1)) hv huv hno
    exact signed_derivative_integrable q q' _ _ huv.le
      (hc.mono (Icc_subset_Icc (hC _ hu).1 (hC _ hv).2)) hd hs
  simpa only [ht0,htn] using IntervalIntegrable.trans_iterate hi

end PaperI.FinitePieceFTC
