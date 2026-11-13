import PaperILean.UniformLocalFrontierCellCover
import PaperILean.OpenArcMonotoneSubdivision
import PaperILean.UniformClosedArcGraph

/-! I1261: apply the checked open cuts to an actual interval graph, and close
each piece without losing the original coordinate parameter or the uniform
image format. Empty/point assembly is handled separately. -/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology

def IsClosedPlanarMonotoneArc (S : Set (Fin 2 → ℝ)) : Prop :=
  ∃ (i : Fin 2) (a b : ℝ) (γ : ℝ → Fin 2 → ℝ), a < b ∧
    ContinuousOn γ (Icc a b) ∧ (∀ t ∈ Icc a b, γ t i = t) ∧
    (∀ k, MonotoneOn (fun t => γ t k) (Icc a b) ∨ AntitoneOn (fun t => γ t k) (Icc a b)) ∧
    S = γ '' Icc a b

theorem closedMonotoneArc_coordinate_eq_parameter {γ : ℝ → Fin 2 → ℝ}
    {a b : ℝ} (hab : a < b) (i : Fin 2) (ht : ∀ t ∈ Ioo a b, γ t i = t)
    {x : ℝ} (hx : x ∈ Icc a b) : closedMonotoneArc γ a b x i = x := by
  apply extendFrom_eq (by simpa only [closure_Ioo hab.ne] using hx)
  have he : (fun t => γ t i) =ᶠ[𝓝[Ioo a b] x] id := by
    filter_upwards [self_mem_nhdsWithin] with t ht'
    exact ht t ht'
  exact continuousWithinAt_id.tendsto.congr' he.symm

theorem bounded_sign_format_open_coordinate_restriction {α : Type*}
    (A : Finset (MvPolynomial α ℝ)) (S : Set (α → ℝ)) (s D : ℕ)
    (hc : A.card ≤ s) (hd : ∀ p ∈ A, p.totalDegree ≤ D)
    (hS : PolynomialSignDetermined A S) (j : α) (a b : ℝ) :
    ∃ B : Finset (MvPolynomial α ℝ), B.card ≤ s + 2 ∧
      (∀ p ∈ B, p.totalDegree ≤ max D 1) ∧
      PolynomialSignDetermined B {x | x ∈ S ∧ x j ∈ Ioo a b} := by
  classical
  let L : MvPolynomial α ℝ := MvPolynomial.X j - MvPolynomial.C a
  let R : MvPolynomial α ℝ := MvPolynomial.C b - MvPolynomial.X j
  have hL : L.totalDegree ≤ 1 := (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  have hR : R.totalDegree ≤ 1 := (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  refine ⟨(A ∪ {L}) ∪ {R}, ?_, ?_, ?_⟩
  · have h1 := Finset.card_union_le A {L}
    have h2 := Finset.card_union_le (A ∪ {L}) {R}
    simp only [Finset.card_singleton] at h1 h2
    omega
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact (hd p hp).trans (le_max_left D 1)
      · rw [Finset.mem_singleton.mp hp]
        exact hL.trans (le_max_right D 1)
    · rw [Finset.mem_singleton.mp hp]
      exact hR.trans (le_max_right D 1)
  · intro x y hxy
    have hs := hS x y (fun p hp => hxy p (Finset.mem_union_left _ (Finset.mem_union_left _ hp)))
    have hl := (hxy L (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)))).2
    have hr := (hxy R (Finset.mem_union_right _ (Finset.mem_singleton_self _))).2
    simp only [L,R,map_sub,MvPolynomial.eval_X,MvPolynomial.eval_C,sub_pos] at hl hr
    exact and_congr hs (and_congr hl hr)

theorem planar_interval_graph_restriction_eq {S : Set (Fin 2 → ℝ)}
    {γ : ℝ → Fin 2 → ℝ} {a b u v : ℝ} (i : Fin 2)
    (ht : ∀ t ∈ Ioo a b, γ t i = t) (himage : S = γ '' Ioo a b)
    (hsub : Ioo u v ⊆ Ioo a b) :
    {x | x ∈ S ∧ x i ∈ Ioo u v} = γ '' Ioo u v := by
  rw [himage]
  ext x
  constructor
  · rintro ⟨⟨t,ht',rfl⟩,hi⟩
    exact ⟨t,by simpa only [ht t ht'] using hi,rfl⟩
  · rintro ⟨t,ht',rfl⟩
    exact ⟨⟨t,hsub ht',rfl⟩,by simpa only [ht t (hsub ht')] using ht'⟩

/-- The count and completed image-format bounds precede the actual interval
graph and its range bounds. This is the original subdivision/completion route. -/
theorem published_uniform_planar_interval_graph_closed_cover
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hMono : PublishedOneVariableMonotonicity)
    (s D : ℕ) :
    ∃ M sOut dOut : ℕ, ∀ (S : Set (Fin 2 → ℝ)) (A : Finset (MvPolynomial (Fin 2) ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      IsPlanarIntervalGraph S →
      (∀ i : Fin 2, BddBelow ((fun x => x i) '' S)) →
      (∀ i : Fin 2, BddAbove ((fun x => x i) '' S)) →
      ∃ (n : ℕ) (C : Fin n → Set (Fin 2 → ℝ)), n ≤ M ∧ (⋃ j, C j) = closure S ∧
        (∀ j, IsClosedPlanarMonotoneArc (C j)) ∧
        ∀ j, ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
          (∀ q ∈ B, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined B (C j) := by
  obtain ⟨M,hM⟩ := published_bounded_open_arc_closed_monotone_cover hCell hHardt hQE hMono
    (Fin 2) (max s 1) (max D 1)
  obtain ⟨sc,dc,hcl⟩ := published_bounded_sign_format_closure_format hQE (Fin 2) (s+2) (max D 1)
  refine ⟨M,sc,dc,?_⟩
  intro S A hAc hAd hA hgraph hlo hhi
  obtain ⟨i,a,b,γ,hab,hcont,hread,himage⟩ := hgraph
  have hlow : ∀ k, BddBelow ((fun t => γ t k) '' Ioo a b) := by
    intro k
    simpa only [himage,image_image,Function.comp_def] using hlo k
  have hhigh : ∀ k, BddAbove ((fun t => γ t k) '' Ioo a b) := by
    intro k
    simpa only [himage,image_image,Function.comp_def] using hhi k
  obtain ⟨n,t,hn,ht0,htn,ht,hpieces,hunion⟩ := hM γ a b hab hcont
    (planar_interval_graph_scalar_format i hread himage A s D hAc hAd hA) hlow hhigh
  let C : Fin n → Set (Fin 2 → ℝ) := fun j =>
    closedMonotoneArc γ (t j.val) (t (j.val+1)) '' Icc (t j.val) (t (j.val+1))
  have hsub (j : Fin n) : Ioo (t j.val) (t (j.val+1)) ⊆ Ioo a b := by
    have h0 := ht ⟨le_rfl,Nat.zero_le n⟩ ⟨Nat.zero_le _,j.isLt.le⟩ (Nat.zero_le _)
    have h1 := ht ⟨Nat.zero_le _,j.isLt⟩ ⟨Nat.zero_le n,le_rfl⟩ j.isLt
    rw [ht0] at h0
    rw [htn] at h1
    exact Ioo_subset_Ioo h0 h1
  refine ⟨n,C,hn,by simpa only [himage] using hunion,?_,?_⟩
  · intro j
    have hp := hpieces j.val j.isLt
    exact ⟨i,t j.val,t (j.val+1),closedMonotoneArc γ (t j.val) (t (j.val+1)),hp.1,hp.2.1,
      fun x hx => closedMonotoneArc_coordinate_eq_parameter hp.1 i (fun t ht' => hread t (hsub j ht')) hx,
      hp.2.2,rfl⟩
  · intro j
    obtain ⟨B,hBc,hBd,hB⟩ := bounded_sign_format_open_coordinate_restriction A S s D hAc hAd hA i
      (t j.val) (t (j.val+1))
    rw [planar_interval_graph_restriction_eq i hread himage (hsub j)] at hB
    obtain ⟨B',hB'c,hB'd,hB'⟩ := hcl B _ hBc hBd hB
    have he : C j = closure (γ '' Ioo (t j.val) (t (j.val+1))) :=
      closed_interval_extension_image_eq_closure (hpieces j.val j.isLt).1 (hpieces j.val j.isLt).2.1
        (fun _ hx => closedMonotoneArc_eq (hcont.mono (hsub j)) hx)
    exact ⟨B',hB'c,hB'd,he ▸ hB'⟩

end PaperI
