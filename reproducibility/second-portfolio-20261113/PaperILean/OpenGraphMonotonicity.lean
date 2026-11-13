import PaperILean.PublishedUniformMonotoneCuts
import PaperILean.OpenIntervalMonotoneCuts

/-! Exact graph/bad-locus correspondence with graph correctness ONLY on Ioo.
Values at both endpoints and outside the interval are unrestricted. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem graphIntervalCondition_realize_iff_open {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (S : Set (Fin 4 → ℝ))
    (p : α → ℝ) (f : ℝ → ℝ) (a b x u v : ℝ)
    (hau : a ≤ u) (hvb : v ≤ b)
    (hG : ∀ t ∈ Ioo a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) :
    Sum.elim (Sum.elim (Sum.elim p ![a,b]) (fun _ : Unit => x)) ![u,v] ∈
      graphIntervalCondition G S ↔
      ∀ t ∈ Ioo u v, ∀ s ∈ Ioo u v, ![t,s,f t,f s] ∈ S := by
  have inside : ∀ t ∈ Ioo u v, t ∈ Ioo a b :=
    fun t ht => ⟨hau.trans_lt ht.1, ht.2.trans_le hvb⟩
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

theorem graphMonotonicityGoodRelation_realize_iff_open {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b x : ℝ)
    (hG : ∀ t ∈ Ioo a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) :
    Sum.elim (Sum.elim p ![a,b]) (fun _ : Unit => x) ∈
      graphMonotonicityGoodRelation G ↔ LocalStrictMonotoneOrConstant f a b x := by
  constructor
  · rintro ⟨w, hau, hvb, hux, hxv, h⟩
    refine ⟨w 0, w 1, hau, hvb, hux, hxv, ?_⟩
    have hw : w = ![w 0,w 1] := by funext i; fin_cases i <;> rfl
    rw [hw] at h
    rcases h with hi | hd | hc
    · left
      have hi' := (graphIntervalCondition_realize_iff_open G increasingGraphComparisons
        p f a b x (w 0) (w 1) hau hvb hG).mp hi
      exact hi'
    · right; left
      have hd' := (graphIntervalCondition_realize_iff_open G decreasingGraphComparisons
        p f a b x (w 0) (w 1) hau hvb hG).mp hd
      exact hd'
    · right; right
      have hc' := (graphIntervalCondition_realize_iff_open G constantGraphComparisons
        p f a b x (w 0) (w 1) hau hvb hG).mp hc
      exact fun s hs => hc' s hs x ⟨hux,hxv⟩
  · rintro ⟨u,v,hau,hvb,hux,hxv,h⟩
    refine ⟨![u,v],hau,hvb,hux,hxv,?_⟩
    rcases h with hi | hd | hc
    · left
      exact (graphIntervalCondition_realize_iff_open G increasingGraphComparisons
        p f a b x u v hau hvb hG).mpr hi
    · right; left
      exact (graphIntervalCondition_realize_iff_open G decreasingGraphComparisons
        p f a b x u v hau hvb hG).mpr hd
    · right; right
      apply (graphIntervalCondition_realize_iff_open G constantGraphComparisons
        p f a b x u v hau hvb hG).mpr
      intro t ht s hs
      exact (hc t ht).trans (hc s hs).symm

theorem graphMonotonicityBadRelation_realize_iff_open {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b x : ℝ)
    (hG : ∀ t ∈ Ioo a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) :
    Sum.elim (Sum.elim p ![a,b]) (fun _ : Unit => x) ∈
      graphMonotonicityBadRelation G ↔ x ∈ MonotonicityBadSet f a b := by
  change (x ∈ Ioo a b ∧ ¬ _ ) ↔ (x ∈ Ioo a b ∧ ¬ _)
  rw [graphMonotonicityGoodRelation_realize_iff_open G p f a b x hG]

theorem openScalarGraph_has_sign_description_of_joint_graph_open
    {α : Type*} {G : Set ((α ⊕ Fin 2) → ℝ)}
    (hG : HasPolynomialSignDescription G) (p : α → ℝ)
    (f : ℝ → ℝ) (a b : ℝ)
    (hGrep : ∀ t ∈ Set.Ioo a b, ∀ y : ℝ,
      Sum.elim p ![t, y] ∈ G ↔ y = f t) :
    HasPolynomialSignDescription (openScalarGraph f a b) := by
  classical
  obtain ⟨A, hA⟩ := hG
  have hSlice := polynomialSignDetermined_projectionFiber p A G hA
  have ha := polynomialSignDetermined_pos
    (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C a)
  have hb := polynomialSignDetermined_pos
    (MvPolynomial.C b - MvPolynomial.X (0 : Fin 2))
  have hEq : openScalarGraph f a b =
      (projectionFiber G p ∩ {x | 0 < MvPolynomial.eval x
        (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C a)}) ∩
      {x | 0 < MvPolynomial.eval x (MvPolynomial.C b - MvPolynomial.X (0 : Fin 2))} := by
    ext v
    have hv : ![v 0, v 1] = v := by
      funext i
      fin_cases i <;> simp
    simp only [Set.mem_inter_iff, projectionFiber, Set.mem_setOf_eq, map_sub,
      MvPolynomial.eval_X, MvPolynomial.eval_C, sub_pos, openScalarGraph]
    constructor
    · rintro ⟨ha, hb, hy⟩
      exact ⟨⟨by simpa only [hv] using (hGrep (v 0) ⟨ha, hb⟩ (v 1)).mpr hy, ha⟩, hb⟩
    · rintro ⟨⟨hmem, ha⟩, hb⟩
      exact ⟨ha, hb, (hGrep (v 0) ⟨ha, hb⟩ (v 1)).mp (by simpa only [hv] using hmem)⟩
  rw [hEq]
  exact ⟨_, polynomialSignDetermined_inter (polynomialSignDetermined_inter hSlice ha) hb⟩

/-- Apply the accepted qualitative QE input to the joint definable relation,
then specialize and restrict it using the local graph identity. -/
theorem published_openScalarGraph_sign_description_open
    (hQE : PublishedRealSemialgebraicity)
    {α : Type} [Finite α] {G : Set ((α ⊕ Fin 2) → ℝ)}
    (hG : (Set.univ : Set ℝ).Definable Language.ring G) (p : α → ℝ)
    (f : ℝ → ℝ) (a b : ℝ)
    (hGrep : ∀ t ∈ Set.Ioo a b, ∀ y : ℝ,
      Sum.elim p ![t, y] ∈ G ↔ y = f t) :
    HasPolynomialSignDescription (openScalarGraph f a b) :=
  openScalarGraph_has_sign_description_of_joint_graph_open
    (hQE.finite_sign_description G hG) p f a b hGrep

theorem scalar_bad_fiber_eq_monotonicityBadSet_open {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ)
    (hG : ∀ t ∈ Ioo a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) :
    scalarProjectionFiber (graphMonotonicityBadRelation G) (Sum.elim p ![a,b]) =
      MonotonicityBadSet f a b := by
  ext x
  exact graphMonotonicityBadRelation_realize_iff_open G p f a b x hG

end PaperI

