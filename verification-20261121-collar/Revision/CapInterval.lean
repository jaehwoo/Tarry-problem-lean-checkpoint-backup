import PaperILean.CommonNullCenteredRoutes

open Set MeasureTheory
noncomputable section

namespace PaperI.CollarRevision

open BoundedCharacteristic CorridorBands ShortProjectionCaps ParabolicCollar

/-- Symmetric padding is needed only when the projected interval is shorter than m. -/
def pad (I : Set ℝ) (m : ℝ) := (max m (horizontalSpan I) - horizontalSpan I) / 2
def capLeft (I : Set ℝ) (m : ℝ) := sInf I - pad I m
def capRight (I : Set ℝ) (m : ℝ) := sSup I + pad I m

theorem cap_length (I : Set ℝ) (m : ℝ) :
    capRight I m - capLeft I m = max m (horizontalSpan I) := by
  unfold capRight capLeft pad horizontalSpan
  ring

theorem cap_geometry {I : Set ℝ} {m : ℝ} (hI : I.Nonempty)
    (hlo : BddBelow I) (hhi : BddAbove I) (hm : 0 ≤ m) :
    I ⊆ Icc (capLeft I m) (capRight I m) ∧
    Icc (capLeft I m) (capRight I m) ⊆ Icc (leftEnd I m) (rightEnd I m) ∧
    rightEnd I m - leftEnd I m ≤ 2 * (capRight I m - capLeft I m) := by
  obtain ⟨hs,hsub⟩ := interval_endpoints hI hlo hhi
  have hspan : 0 ≤ horizontalSpan I := sub_nonneg.mpr hs
  have hpad : 0 ≤ pad I m := by unfold pad; linarith [le_max_right m (horizontalSpan I)]
  have hupper : pad I m ≤ m/2 := by
    unfold pad
    rcases le_total m (horizontalSpan I) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  refine ⟨?_,?_,?_⟩
  · intro x hx
    exact ⟨by dsimp [capLeft]; linarith [(hsub hx).1],
      by dsimp [capRight]; linarith [(hsub hx).2]⟩
  · intro x hx
    rcases hx with ⟨ha,hb⟩
    exact ⟨by dsimp [capLeft,leftEnd] at *; linarith,
      by dsimp [capRight,rightEnd] at *; linarith⟩
  · rw [cap_length]
    unfold leftEnd rightEnd
    linarith [show m ≤ max m (horizontalSpan I) from le_max_left ..,
      show sSup I - sInf I ≤ max m (horizontalSpan I) from le_max_right ..]

theorem projection_bounded {E Ω : Set Plane} {d v : Plane → ℝ} {keep : Plane → Prop}
    {P m τ Λ : ℝ} {K k Cf H sf df n : ℕ} {ι : Type} [DecidableEq ι]
    {F : Plane → ℝ → ℝ} {labels : Finset ι} {rep : ι → Plane}
    (cap : PhaseCap P m τ Λ K k Cf H sf df n E Ω d v keep F labels rep)
    (hτ : 0 < τ) (hE : ∃ R, ∀ q ∈ E, |q.1| ≤ R ∧ |q.2| ≤ R) :
    BddBelow (project Ω F '' Ω) ∧ BddAbove (project Ω F '' Ω) := by
  obtain ⟨R,hR⟩ := hE
  have hb (x : ℝ) (hx : x ∈ project Ω F '' Ω) : |x| ≤ R := by
    obtain ⟨p,hp,rfl⟩ := hx
    obtain ⟨ht,_,hsol⟩ := cap.time p hp
    have hW : midheight Ω - p.2 ∈ window τ := abs_le.mp (ht.le.trans (by linarith))
    exact (hR _ (hsol _ hW).1).1
  exact ⟨⟨-R,fun x hx => (abs_le.mp (hb x hx)).1⟩,⟨R,fun x hx => (abs_le.mp (hb x hx)).2⟩⟩

/-- Each original label is reached from its actual closed-seed coordinate. -/
theorem exact_seed_reaches {E Ω : Set Plane} {d v : Plane → ℝ} {keep : Plane → Prop}
    {P m τ Λ : ℝ} {K k Cf H sf df n : ℕ} {ι : Type} [DecidableEq ι]
    {F : Plane → ℝ → ℝ} {labels : Finset ι} {rep : ι → Plane}
    (cap : PhaseCap P m τ Λ K k Cf H sf df n E Ω d v keep F labels rep) (hm : 0 ≤ m)
    (hτ : 0 < τ) (hE : ∃ R, ∀ q ∈ E, |q.1| ≤ R ∧ |q.2| ≤ R)
    (hΩ : Ω.Nonempty) (hr : ∀ i ∈ labels, rep i ∈ Ω) :
    let I := project Ω F '' Ω
    let J := Icc (capLeft I m) (capRight I m)
    ∃ Y : ℝ → ℝ → ℝ, (∀ u ∈ J, Y u 0 = u ∧ DirectedSolution E d (midheight Ω) 1 (-τ) τ (Y u)) ∧
      ∀ i ∈ labels, project Ω F (rep i) ∈ J ∧
        rep i = point (Y (project Ω F (rep i))) (midheight Ω) ((rep i).2 - midheight Ω) ∧
        |(rep i).2 - midheight Ω| < τ/2 := by
  dsimp only
  obtain ⟨hlo,hhi⟩ := projection_bounded cap hτ hE
  obtain ⟨hIn,hSub,_⟩ := cap_geometry (hΩ.image _) hlo hhi hm
  obtain ⟨Y,hY,hRep⟩ := cap.actual_reaches
  exact ⟨Y,fun u hu => hY u (hSub hu),fun i hi => ⟨hIn ⟨rep i,hr i hi,rfl⟩,(hRep i hi).2⟩⟩

end PaperI.CollarRevision
