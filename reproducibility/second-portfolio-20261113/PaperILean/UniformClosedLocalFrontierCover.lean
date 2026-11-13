import PaperILean.ClosedPlanarCellCover

/-! I1261: assemble the actual local frontier from uniformly many closed
coordinate-monotone semialgebraic arcs and points. Empty slots are permitted
and counted. This is a cover, not an asserted disjoint partition. -/
noncomputable section
namespace PaperI
open Set

theorem bounded_finite_cover_refinement {X : Type*} {n K : ℕ}
    (C : Fin n → Set X) (P : Set X → Prop) (hempty : P ∅)
    (href : ∀ j, ∃ (m : ℕ) (D : Fin m → Set X), m ≤ K ∧ (⋃ k, D k) = C j ∧ ∀ k, P (D k)) :
    ∃ F : Fin (n*K) → Set X, (⋃ k, F k) = ⋃ j, C j ∧ ∀ k, P (F k) := by
  classical
  choose m D hm hcover hgood using href
  let e : Fin n × Fin K ≃ Fin (n*K) := finProdFinEquiv
  let G : Fin n × Fin K → Set X := fun jk =>
    if h : jk.2.val < m jk.1 then D jk.1 ⟨jk.2.val,h⟩ else ∅
  let F : Fin (n*K) → Set X := fun k => G (e.symm k)
  refine ⟨F,?_,?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := mem_iUnion.mp hx
      by_cases h : (e.symm k).2.val < m (e.symm k).1
      · have hd : x ∈ D (e.symm k).1 ⟨(e.symm k).2.val,h⟩ := by simpa only [F,G,dif_pos h] using hk
        apply mem_iUnion.mpr
        refine ⟨(e.symm k).1,?_⟩
        rw [← hcover]
        exact mem_iUnion.mpr ⟨_,hd⟩
      · simpa only [F,G,dif_neg h,mem_empty_iff_false] using hk
    · intro hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      rw [← hcover j] at hj
      obtain ⟨k,hk⟩ := mem_iUnion.mp hj
      refine mem_iUnion.mpr ⟨e (j,⟨k.val,k.isLt.trans_le (hm j)⟩),?_⟩
      change x ∈ G (e.symm (e (j,⟨k.val,k.isLt.trans_le (hm j)⟩)))
      rw [e.symm_apply_apply]
      simpa only [G,dif_pos k.isLt] using hk
  · intro k
    by_cases h : (e.symm k).2.val < m (e.symm k).1
    · simpa only [F,G,dif_pos h] using hgood (e.symm k).1 ⟨(e.symm k).2.val,h⟩
    · simpa only [F,G,dif_neg h] using hempty

/-- Joint graph-format control for the closed arcs follows from their actual
image format and the retained original-coordinate parameter. -/
theorem IsClosedPlanarMonotoneArc.exists_bounded_joint_graph
    {S : Set (Fin 2 → ℝ)} (h : IsClosedPlanarMonotoneArc S)
    (A : Finset (MvPolynomial (Fin 2) ℝ)) (s D : ℕ) (hc : A.card ≤ s)
    (hd : ∀ q ∈ A, q.totalDegree ≤ D) (hA : PolynomialSignDetermined A S) :
    ∃ (i : Fin 2) (a b : ℝ) (γ : ℝ → Fin 2 → ℝ), a < b ∧
      ContinuousOn γ (Icc a b) ∧ (∀ t ∈ Icc a b, γ t i = t) ∧
      (∀ k, MonotoneOn (fun t => γ t k) (Icc a b) ∨ AntitoneOn (fun t => γ t k) (Icc a b)) ∧
      S = γ '' Icc a b ∧
      ∃ B : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ), B.card ≤ s+1 ∧
        (∀ q ∈ B, q.totalDegree ≤ max D 1) ∧
        PolynomialSignDetermined B (parametrizedArcGraph γ (Icc a b)) := by
  obtain ⟨i,a,b,γ,hab,hc',ht,hm,he⟩ := h
  exact ⟨i,a,b,γ,hab,hc',ht,hm,he,planar_interval_graph_joint_format i ht he A s D hc hd hA⟩

/-- Uniform closed-arc/point cover of the unchanged actual Euclidean local
frontier. All three bounds precede E, its coefficients, the center and radius. -/
theorem published_uniform_closed_localFrontier_cover
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hMono : PublishedOneVariableMonotonicity)
    (s D : ℕ) :
    ∃ M sOut dOut : ℕ, ∀ (E : Set (WithLp 2 (Fin 2 → ℝ)))
      (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) → IsOpen E →
      ∀ (z : WithLp 2 (Fin 2 → ℝ)) (R : ℝ),
      ∃ (n : ℕ) (C : Fin n → Set (Fin 2 → ℝ)), n ≤ M ∧
        (⋃ j, C j) = (WithLp.equiv 2 (Fin 2 → ℝ)) '' (frontier E ∩ Metric.closedBall z R) ∧
        (∀ j, C j = ∅ ∨ (∃ x, C j = {x}) ∨ IsClosedPlanarMonotoneArc (C j)) ∧
        ∀ j, ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
          (∀ q ∈ B, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined B (C j) := by
  classical
  obtain ⟨M,sp,dp,hcover⟩ := published_uniform_localFrontier_cell_cover hCAD hQE s D
  obtain ⟨K,sc,dc,hclose⟩ := published_uniform_planar_interval_graph_closed_cover hCell hHardt hQE hMono sp dp
  refine ⟨M*(K+1),max sp sc,max dp dc,?_⟩
  intro E A hAc hAd hA hE z R
  obtain ⟨n,C,hn,hunion,hcases,hfmt⟩ := hcover E A hAc hAd hA hE z R
  let S := (WithLp.equiv 2 (Fin 2 → ℝ)) '' (frontier E ∩ Metric.closedBall z R)
  let P : Set (Fin 2 → ℝ) → Prop := fun T =>
    (T = ∅ ∨ (∃ x, T = {x}) ∨ IsClosedPlanarMonotoneArc T) ∧
    ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ max sp sc ∧
      (∀ q ∈ B, q.totalDegree ≤ max dp dc) ∧ PolynomialSignDetermined B T
  have hpempty : P ∅ := ⟨Or.inl rfl,∅,by simp,by simp,polynomialSignDetermined_empty⟩
  have hsub (j : Fin n) : C j ⊆ S := by
    dsimp only [S]
    rw [← hunion]
    exact subset_iUnion C j
  obtain ⟨hlo,hhi⟩ := localFrontier_coordinates_bounded E z R
  have href (j : Fin n) : ∃ (m : ℕ) (G : Fin m → Set (Fin 2 → ℝ)),
      m ≤ K+1 ∧ (⋃ k, G k) = closure (C j) ∧ ∀ k, P (G k) := by
    obtain ⟨B,hBc,hBd,hB⟩ := hfmt j
    rcases hcases j with he | ⟨x,hx⟩ | hg
    · refine ⟨0,Fin.elim0,Nat.zero_le _,?_,fun k => Fin.elim0 k⟩
      simp only [he,closure_empty,iUnion_of_empty]
    · refine ⟨1,fun _ => C j,by omega,?_,?_⟩
      · simp only [hx,closure_singleton,iUnion_const]
      · intro k
        exact ⟨Or.inr (Or.inl ⟨x,hx⟩),B,hBc.trans (le_max_left sp sc),
          fun q hq => (hBd q hq).trans (le_max_left dp dc),hB⟩
    · obtain ⟨m,G,hm,hunion',harcs,hfmt'⟩ := hclose (C j) B hBc hBd hB hg
        (fun i => (hlo i).mono (image_mono (hsub j)))
        (fun i => (hhi i).mono (image_mono (hsub j)))
      refine ⟨m,G,hm.trans (Nat.le_succ K),hunion',?_⟩
      intro k
      obtain ⟨B',hB'c,hB'd,hB'⟩ := hfmt' k
      exact ⟨Or.inr (Or.inr (harcs k)),B',hB'c.trans (le_max_right sp sc),
        fun q hq => (hB'd q hq).trans (le_max_right dp dc),hB'⟩
  obtain ⟨F,hF,hP⟩ := bounded_finite_cover_refinement (fun j => closure (C j)) P hpempty href
  refine ⟨n*(K+1),F,Nat.mul_le_mul_right (K+1) hn,?_,fun k => (hP k).1,fun k => (hP k).2⟩
  rw [hF,← closure_iUnion_of_finite,hunion]
  exact ((localFrontier_isCompact E z R).image planarCoordinatesHomeomorph.continuous).isClosed.closure_eq

end PaperI
