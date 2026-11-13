import PaperILean.GraphMonotonicityDefinability

/-! Exact correspondence between the definable graph construction and the
actual exceptional locus. Graph correctness is needed only on `[a,b]`;
endpoints and parameters retain their roles as free coordinates. -/

noncomputable section
namespace PaperI
open Set

theorem graphIntervalCondition_realize_iff {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (S : Set (Fin 4 → ℝ))
    (p : α → ℝ) (f : ℝ → ℝ) (a b x u v : ℝ)
    (hau : a ≤ u) (hvb : v ≤ b)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) :
    Sum.elim (Sum.elim (Sum.elim p ![a,b]) (fun _ : Unit => x)) ![u,v] ∈
      graphIntervalCondition G S ↔
      ∀ t ∈ Ioo u v, ∀ s ∈ Ioo u v, ![t,s,f t,f s] ∈ S := by
  have inside : ∀ t ∈ Ioo u v, t ∈ Icc a b :=
    fun t ht => ⟨hau.trans ht.1.le, ht.2.le.trans hvb⟩
  change (∀ q : Fin 4 → ℝ, q 0 ∈ Ioo u v → q 1 ∈ Ioo u v →
    Sum.elim p ![q 0,q 2] ∈ G → Sum.elim p ![q 1,q 3] ∈ G → q ∈ S) ↔ _
  constructor
  · intro h t ht s hs
    exact h ![t,s,f t,f s] ht hs ((hG t (inside t ht) (f t)).mpr rfl)
      ((hG s (inside s hs) (f s)).mpr rfl)
  · intro h q ht hs hyt hys
    have hyt' := (hG (q 0) (inside _ ht) (q 2)).mp hyt
    have hys' := (hG (q 1) (inside _ hs) (q 3)).mp hys
    have he : ![q 0,q 1,f (q 0),f (q 1)] = q := by
      funext i
      fin_cases i <;> simp [hyt', hys']
    simpa only [he] using h (q 0) ht (q 1) hs

theorem graphMonotonicityGoodRelation_realize_iff {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b x : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) :
    Sum.elim (Sum.elim p ![a,b]) (fun _ : Unit => x) ∈
      graphMonotonicityGoodRelation G ↔ LocalStrictMonotoneOrConstant f a b x := by
  constructor
  · rintro ⟨w, hau, hvb, hux, hxv, h⟩
    refine ⟨w 0, w 1, hau, hvb, hux, hxv, ?_⟩
    have hw : w = ![w 0,w 1] := by funext i; fin_cases i <;> rfl
    rw [hw] at h
    rcases h with hi | hd | hc
    · left
      have hi' := (graphIntervalCondition_realize_iff G increasingGraphComparisons
        p f a b x (w 0) (w 1) hau hvb hG).mp hi
      exact hi'
    · right; left
      have hd' := (graphIntervalCondition_realize_iff G decreasingGraphComparisons
        p f a b x (w 0) (w 1) hau hvb hG).mp hd
      exact hd'
    · right; right
      have hc' := (graphIntervalCondition_realize_iff G constantGraphComparisons
        p f a b x (w 0) (w 1) hau hvb hG).mp hc
      exact fun s hs => hc' s hs x ⟨hux,hxv⟩
  · rintro ⟨u,v,hau,hvb,hux,hxv,h⟩
    refine ⟨![u,v],hau,hvb,hux,hxv,?_⟩
    rcases h with hi | hd | hc
    · left
      exact (graphIntervalCondition_realize_iff G increasingGraphComparisons
        p f a b x u v hau hvb hG).mpr hi
    · right; left
      exact (graphIntervalCondition_realize_iff G decreasingGraphComparisons
        p f a b x u v hau hvb hG).mpr hd
    · right; right
      apply (graphIntervalCondition_realize_iff G constantGraphComparisons
        p f a b x u v hau hvb hG).mpr
      intro t ht s hs
      exact (hc t ht).trans (hc s hs).symm

theorem graphMonotonicityBadRelation_realize_iff {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b x : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) :
    Sum.elim (Sum.elim p ![a,b]) (fun _ : Unit => x) ∈
      graphMonotonicityBadRelation G ↔ x ∈ MonotonicityBadSet f a b := by
  change (x ∈ Ioo a b ∧ ¬ _ ) ↔ (x ∈ Ioo a b ∧ ¬ _)
  rw [graphMonotonicityGoodRelation_realize_iff G p f a b x hG]

end PaperI
