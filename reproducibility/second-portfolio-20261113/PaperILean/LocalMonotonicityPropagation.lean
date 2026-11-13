import PaperILean.MonotonicityBadSet
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.Compact

/-! Local strict increase, strict decrease and constancy propagate on a connected
real interval. No semialgebraic or published input is used here. Weak local
monotone-or-antitone is insufficient across a constant plateau. This topological
proof is separate from the manuscript's derivative-sign intermediate argument. -/

noncomputable section
namespace PaperI
open Set

/-- Points possessing an open interval with a specified property. -/
def LocalIntervalLocus (P : Set ℝ → Prop) : Set ℝ :=
  {x | ∃ l r : ℝ, l < x ∧ x < r ∧ P (Ioo l r)}

theorem isOpen_localIntervalLocus (P : Set ℝ → Prop) :
    IsOpen (LocalIntervalLocus P) := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro x ⟨l, r, hl, hr, hP⟩
  exact ⟨Ioo l r, fun y hy => ⟨l, r, hy.1, hy.2, hP⟩, isOpen_Ioo, hl, hr⟩

theorem disjoint_local_strictMono_strictAnti (f : ℝ → ℝ) :
    Disjoint (LocalIntervalLocus (StrictMonoOn f))
      (LocalIntervalLocus (StrictAntiOn f)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨l, r, hl, hr, hm⟩ ⟨l', r', hl', hr', ha⟩
  obtain ⟨y, hxy, hyr⟩ := exists_between (lt_min hr hr')
  have h1 := hm ⟨hl, hr⟩ ⟨hl.trans hxy, hyr.trans_le (min_le_left _ _)⟩ hxy
  have h2 := ha ⟨hl', hr'⟩ ⟨hl'.trans hxy, hyr.trans_le (min_le_right _ _)⟩ hxy
  exact (not_lt_of_ge h1.le) h2

theorem disjoint_local_strictMono_constant (f : ℝ → ℝ) :
    Disjoint (LocalIntervalLocus (StrictMonoOn f))
      (LocalIntervalLocus (fun S => ∀ x ∈ S, ∀ y ∈ S, f x = f y)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨l, r, hl, hr, hm⟩ ⟨l', r', hl', hr', hc⟩
  obtain ⟨y, hxy, hyr⟩ := exists_between (lt_min hr hr')
  have h1 := hm ⟨hl, hr⟩ ⟨hl.trans hxy, hyr.trans_le (min_le_left _ _)⟩ hxy
  exact (ne_of_lt h1) (hc x ⟨hl', hr'⟩ y ⟨hl'.trans hxy, hyr.trans_le (min_le_right _ _)⟩)

theorem disjoint_local_strictAnti_constant (f : ℝ → ℝ) :
    Disjoint (LocalIntervalLocus (StrictAntiOn f))
      (LocalIntervalLocus (fun S => ∀ x ∈ S, ∀ y ∈ S, f x = f y)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨l, r, hl, hr, hm⟩ ⟨l', r', hl', hr', hc⟩
  obtain ⟨y, hxy, hyr⟩ := exists_between (lt_min hr hr')
  have h1 := hm ⟨hl, hr⟩ ⟨hl.trans hxy, hyr.trans_le (min_le_left _ _)⟩ hxy
  exact (ne_of_lt h1) (hc y ⟨hl'.trans hxy, hyr.trans_le (min_le_right _ _)⟩ x ⟨hl', hr'⟩)

/-- A continuous function locally strictly increasing everywhere on an interval
is globally monotone there. A maximum on each compact subinterval proves this. -/
theorem monotoneOn_of_local_strictMono {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Ioo a b))
    (hlocal : Ioo a b ⊆ LocalIntervalLocus (StrictMonoOn f)) :
    MonotoneOn f (Ioo a b) := by
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Ioo a b := fun z hz =>
    ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hxy) (hf.mono hsub)
  have hzy : z = y := by
    by_contra hne
    have hlt : z < y := lt_of_le_of_ne hz.2 hne
    obtain ⟨l, r, hl, hr, hm⟩ := hlocal (hsub hz)
    obtain ⟨w, hzw, hwr⟩ := exists_between (lt_min hlt hr)
    have hw : w ∈ Icc x y := ⟨hz.1.trans hzw.le, (hwr.trans_le (min_le_left _ _)).le⟩
    have hinc := hm ⟨hl, hr⟩ ⟨hl.trans hzw, hwr.trans_le (min_le_right _ _)⟩ hzw
    exact (not_lt_of_ge (hmax hw)) hinc
  subst z
  exact hmax ⟨le_rfl, hxy⟩

theorem antitoneOn_of_local_strictAnti {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Ioo a b))
    (hlocal : Ioo a b ⊆ LocalIntervalLocus (StrictAntiOn f)) :
    AntitoneOn f (Ioo a b) := by
  have hneg : Ioo a b ⊆ LocalIntervalLocus (StrictMonoOn (fun x => - f x)) := by
    rintro x hx
    obtain ⟨l, r, hl, hr, hm⟩ := hlocal hx
    refine ⟨l, r, hl, hr, ?_⟩
    intro y hy z hz hyz
    exact neg_lt_neg (hm hy hz hyz)
  have h := monotoneOn_of_local_strictMono hf.neg hneg
  intro x hx y hy hxy
  exact neg_le_neg_iff.mp (h hx hy hxy)

theorem eqOn_of_local_constant {f : ℝ → ℝ} {a b : ℝ}
    (hlocal : Ioo a b ⊆ LocalIntervalLocus
      (fun S => ∀ x ∈ S, ∀ y ∈ S, f x = f y)) :
    ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, f x = f y := by
  let F : Ioo a b → ℝ := fun x => f x
  have hF : IsLocallyConstant F := by
    apply (IsLocallyConstant.iff_exists_open F).mpr
    intro x
    obtain ⟨l, r, hl, hr, hc⟩ := hlocal x.property
    refine ⟨Subtype.val ⁻¹' Ioo l r, isOpen_Ioo.preimage continuous_subtype_val, ⟨hl, hr⟩, ?_⟩
    intro y hy
    exact hc y hy x ⟨hl, hr⟩
  letI : PreconnectedSpace (Ioo a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  intro x hx y hy
  exact hF.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

/-- No bad points on a subinterval implies one global weak monotonicity direction.
The statement also handles empty and singleton interiors, without `u < v`. -/
theorem monotoneOn_or_antitoneOn_of_no_bad_points {f : ℝ → ℝ} {a b u v : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hau : a ≤ u) (hvb : v ≤ b)
    (hbad : ∀ x ∈ Ioo u v, x ∉ MonotonicityBadSet f a b) :
    MonotoneOn f (Ioo u v) ∨ AntitoneOn f (Ioo u v) := by
  let U := LocalIntervalLocus (StrictMonoOn f)
  let D := LocalIntervalLocus (StrictAntiOn f)
  let C := LocalIntervalLocus (fun S => ∀ x ∈ S, ∀ y ∈ S, f x = f y)
  have hcover : Ioo u v ⊆ U ∪ (D ∪ C) := by
    intro x hx
    have hab : x ∈ Ioo a b := ⟨hau.trans_lt hx.1, hx.2.trans_le hvb⟩
    obtain ⟨l, r, _, _, hl, hr, hm | hm | hc⟩ :=
      (not_mem_monotonicityBadSet_iff hab).mp (hbad x hx)
    · exact Or.inl ⟨l, r, hl, hr, hm⟩
    · exact Or.inr (Or.inl ⟨l, r, hl, hr, hm⟩)
    · exact Or.inr (Or.inr ⟨l, r, hl, hr, fun y hy z hz => (hc y hy).trans (hc z hz).symm⟩)
  have hUD : Disjoint U D := disjoint_local_strictMono_strictAnti f
  have hUC : Disjoint U C := disjoint_local_strictMono_constant f
  have hDC : Disjoint D C := disjoint_local_strictAnti_constant f
  have hcont : ContinuousOn f (Ioo u v) := hf.mono (fun x hx =>
    ⟨hau.trans hx.1.le, hx.2.le.trans hvb⟩)
  rcases IsPreconnected.subset_or_subset (isOpen_localIntervalLocus _)
      ((isOpen_localIntervalLocus _).union (isOpen_localIntervalLocus _))
      (disjoint_union_right.mpr ⟨hUD, hUC⟩) hcover isPreconnected_Ioo with hU | hDCover
  · exact Or.inl (monotoneOn_of_local_strictMono hcont hU)
  · rcases IsPreconnected.subset_or_subset (isOpen_localIntervalLocus _)
        (isOpen_localIntervalLocus _) hDC hDCover isPreconnected_Ioo with hD | hC
    · exact Or.inr (antitoneOn_of_local_strictAnti hcont hD)
    · exact Or.inl (fun x hx y hy _ => (eqOn_of_local_constant hC x hx y hy).le)

end PaperI
