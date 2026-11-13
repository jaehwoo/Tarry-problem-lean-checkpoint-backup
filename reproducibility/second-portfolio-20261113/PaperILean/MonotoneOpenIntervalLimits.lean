import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Tactic

/-! I1261: endpoint limits after the manuscript's coordinate-monotone split.
Boundedness and interior continuity are retained. A collapsed open interval
does not determine a point arc, so the extension theorem requires a < b. -/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology

theorem bounded_monotone_or_antitone_endpoint_limits
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hm : MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b))
    (hlo : BddBelow (f '' Ioo a b)) (hhi : BddAbove (f '' Ioo a b)) :
    ∃ l r : ℝ, Tendsto f (𝓝[>] a) (𝓝 l) ∧ Tendsto f (𝓝[<] b) (𝓝 r) := by
  rcases hm with hm | hm
  · exact ⟨sInf (f '' Ioo a b), sSup (f '' Ioo a b),
      hm.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hab) hlo,
      hm.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hab) hhi⟩
  · exact ⟨sSup (f '' Ioo a b), sInf (f '' Ioo a b),
      hm.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hab) hhi,
      hm.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hab) hlo⟩

theorem bounded_monotone_extendFrom_continuousOn
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hc : ContinuousOn f (Ioo a b))
    (hm : MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b))
    (hlo : BddBelow (f '' Ioo a b)) (hhi : BddAbove (f '' Ioo a b)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Icc a b) := by
  obtain ⟨l, r, hl, hr⟩ := bounded_monotone_or_antitone_endpoint_limits hab hm hlo hhi
  exact continuousOn_Icc_extendFrom_Ioo hab.ne hc hl hr

theorem monotoneOn_extendFrom_Ioo {β : Type*} [ConditionallyCompleteLinearOrder β]
    [TopologicalSpace β] [OrderTopology β] {f : ℝ → β} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Ioo a b)) (hm : MonotoneOn f (Ioo a b))
    (hlo : BddBelow (f '' Ioo a b)) (hhi : BddAbove (f '' Ioo a b)) :
    MonotoneOn (extendFrom (Ioo a b) f) (Icc a b) := by
  have hn := nonempty_Ioo.mpr hab
  have ha := eq_lim_at_left_extendFrom_Ioo hab (hm.tendsto_nhdsWithin_Ioo_right hn hlo)
  have hb := eq_lim_at_right_extendFrom_Ioo hab (hm.tendsto_nhdsWithin_Ioo_left hn hhi)
  intro x hx y hy hxy
  by_cases hxb : x = b
  · have hyb : y = b := le_antisymm hy.2 (hxb ▸ hxy)
    simp [hxb, hyb]
  by_cases hya : y = a
  · have hxa : x = a := le_antisymm (hya ▸ hxy) hx.1
    simp [hxa, hya]
  have hxb' : x < b := lt_of_le_of_ne hx.2 hxb
  have hya' : a < y := lt_of_le_of_ne hy.1 (Ne.symm hya)
  by_cases hxa : x = a
  · rw [hxa, ha]
    by_cases hyb : y = b
    · rw [hyb, hb]
      exact csInf_le_csSup hlo hhi (hn.image f)
    · rw [extendFrom_extends hc y ⟨hya', lt_of_le_of_ne hy.2 hyb⟩]
      exact csInf_le hlo (mem_image_of_mem f ⟨hya', lt_of_le_of_ne hy.2 hyb⟩)
  have hx' : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), hxb'⟩
  rw [extendFrom_extends hc x hx']
  by_cases hyb : y = b
  · rw [hyb, hb]
    exact le_csSup hhi (mem_image_of_mem f hx')
  · rw [extendFrom_extends hc y ⟨hya', lt_of_le_of_ne hy.2 hyb⟩]
    exact hm hx' ⟨hya', lt_of_le_of_ne hy.2 hyb⟩ hxy

theorem antitoneOn_extendFrom_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Ioo a b)) (hm : AntitoneOn f (Ioo a b))
    (hlo : BddBelow (f '' Ioo a b)) (hhi : BddAbove (f '' Ioo a b)) :
    AntitoneOn (extendFrom (Ioo a b) f) (Icc a b) :=
  monotoneOn_extendFrom_Ioo (β := ℝᵒᵈ) hab hc hm hhi hlo

theorem monotone_or_antitone_extendFrom_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Ioo a b))
    (hm : MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b))
    (hlo : BddBelow (f '' Ioo a b)) (hhi : BddAbove (f '' Ioo a b)) :
    MonotoneOn (extendFrom (Ioo a b) f) (Icc a b) ∨
      AntitoneOn (extendFrom (Ioo a b) f) (Icc a b) := by
  rcases hm with hm | hm
  · exact Or.inl (monotoneOn_extendFrom_Ioo hab hc hm hlo hhi)
  · exact Or.inr (antitoneOn_extendFrom_Ioo hab hc hm hlo hhi)

end PaperI
