import PaperILean.CurveGermRestriction
import PaperILean.CellChartPathGraph

/-! Exact graph of a rescaled initial segment of a supplied joint curve family.
The one old-time witness is shared by every output coordinate. Qualitative QE
is used only for finite sign descriptions. Specializing one resulting graph
gives bounds before all parameters, radii, represented curves and endpoints.
The existence of a joint curve-selection family is not proved or assumed as
a global contract. It remains a separate manuscript application obligation. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def curveGermGraph {κ : Type*} (ε : ℝ) (g : ℝ → κ → ℝ) :
    Set ((Unit ⊕ κ) → ℝ) :=
  {v | v (Sum.inl ()) ∈ Ico (0 : ℝ) ε ∧
    (fun k => v (Sum.inr k)) = g (v (Sum.inl ()))}

def rescaledGermRelation {ρ κ : Type*}
    (G : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ)) :
    Set (((ρ ⊕ Unit) ⊕ (Unit ⊕ κ)) → ℝ) :=
  {v | v (Sum.inr (Sum.inl ())) ∈ Icc (0 : ℝ) 1 ∧
    ∃ w : Unit → ℝ, w () = v (Sum.inl (Sum.inr ())) * v (Sum.inr (Sum.inl ())) ∧
      Sum.elim (fun i => v (Sum.inl (Sum.inl i)))
        (Sum.elim w (fun k => v (Sum.inr (Sum.inr k)))) ∈ G}

theorem rescaledGermRelation_definable {ρ κ : Type*} [Finite ρ] [Finite κ]
    {G : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (rescaledGermRelation G) := by
  let δ := (ρ ⊕ Unit) ⊕ (Unit ⊕ κ)
  let e : ρ ⊕ (Unit ⊕ κ) → δ ⊕ Unit :=
    Sum.elim (fun i => Sum.inl (Sum.inl (Sum.inl i)))
      (Sum.elim (fun _ => Sum.inr ()) (fun k => Sum.inl (Sum.inr (Sum.inr k))))
  let Q : MvPolynomial (δ ⊕ Unit) ℝ :=
    MvPolynomial.X (Sum.inr ()) -
      MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr ()))) *
      MvPolynomial.X (Sum.inl (Sum.inr (Sum.inl ())))
  have h := realDefinable_exists ((realPolynomial_zero_definable Q).inter (hG.preimage_comp e))
  have ht : (univ : Set ℝ).Definable Language.ring
      {v : δ → ℝ | v (Sum.inr (Sum.inl ())) ∈ Icc (0 : ℝ) 1} := by
    have h0 := realPolynomial_nonneg_definable
      (MvPolynomial.X (Sum.inr (Sum.inl ())) : MvPolynomial δ ℝ)
    have h1 := realPolynomial_nonneg_definable
      (1 - MvPolynomial.X (Sum.inr (Sum.inl ())) : MvPolynomial δ ℝ)
    simpa only [Set.inter_def, Set.mem_setOf_eq, MvPolynomial.eval_X, map_sub, map_one,
      sub_nonneg, Set.mem_Icc] using h0.inter h1
  convert ht.inter h using 1
  ext v
  apply and_congr_right
  intro _
  apply exists_congr
  intro w
  have he : Sum.elim v w ∘ e =
      Sum.elim (fun i => v (Sum.inl (Sum.inl i)))
        (Sum.elim w (fun k => v (Sum.inr (Sum.inr k)))) := by
    funext i
    rcases i with i | i
    · rfl
    rcases i with ⟨⟩ | i <;> rfl
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, he,
    Q, map_sub, map_mul, MvPolynomial.eval_X, Sum.elim_inr, Sum.elim_inl, sub_eq_zero]

theorem rescaledGermRelation_fiber {ρ κ : Type*}
    (G : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ)) (p : ρ → ℝ)
    (ε r : ℝ) (g : ℝ → κ → ℝ)
    (hG : projectionFiber G p = curveGermGraph ε g) (hr : 0 ≤ r) (hrε : r < ε) :
    projectionFiber (rescaledGermRelation G) (Sum.elim p (fun _ => r)) =
      unitPathGraph (curveInitialSegment g r) := by
  ext v
  change (v (Sum.inl ()) ∈ Icc (0 : ℝ) 1 ∧
    ∃ w : Unit → ℝ, w () = r * v (Sum.inl ()) ∧
      Sum.elim p (Sum.elim w (fun k => v (Sum.inr k))) ∈ G) ↔ _
  constructor
  · rintro ⟨ht,w,hw,hv⟩
    have hmem : Sum.elim w (fun k => v (Sum.inr k)) ∈ curveGermGraph ε g := by
      rw [← hG]
      exact hv
    change w () ∈ Ico (0 : ℝ) ε ∧ (fun k => v (Sum.inr k)) = g (w ()) at hmem
    exact ⟨ht, by simpa only [curveInitialSegment, hw] using hmem.2⟩
  · rintro ⟨ht,hv⟩
    refine ⟨ht,fun _ => r * v (Sum.inl ()),rfl,?_⟩
    change Sum.elim (fun _ : Unit => r * v (Sum.inl ()))
      (fun k => v (Sum.inr k)) ∈ projectionFiber G p
    rw [hG]
    exact ⟨initialSegment_time_mem hr hrε ht,hv⟩

theorem published_rescaledGermRelation_semialgebraic
    (hQE : PublishedRealSemialgebraicity) {ρ κ : Type} [Finite ρ] [Finite κ]
    {G : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ)} (hG : HasPolynomialSignDescription G) :
    HasPolynomialSignDescription (rescaledGermRelation G) :=
  hQE.finite_sign_description _
    (rescaledGermRelation_definable (hasPolynomialSignDescription_definable hG))

/-- Uniformity is across fibers of the fixed joint graph G, not across unrelated
pointwise choices. No positivity of the cell dimension or nonempty parameter
type is imposed. Degree drops and zero/repeated atoms are permitted. -/
theorem published_curveGermFamily_initialSegment_format
    (hQE : PublishedRealSemialgebraicity) {ρ κ : Type} [Finite ρ] [Finite κ]
    (G : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ)) (hG : HasPolynomialSignDescription G) :
    ∃ sPath dPath : ℕ, ∀ (p : ρ → ℝ) (ε r : ℝ) (g : ℝ → κ → ℝ),
      projectionFiber G p = curveGermGraph ε g → 0 ≤ r → r < ε →
      ∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ), A.card ≤ sPath ∧
        (∀ q ∈ A, q.totalDegree ≤ dPath) ∧
        PolynomialSignDetermined A (unitPathGraph (curveInitialSegment g r)) := by
  obtain ⟨sPath,dPath,h⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format
    (published_rescaledGermRelation_semialgebraic hQE hG)
  refine ⟨sPath,dPath,?_⟩
  intro p ε r g hgraph hr hrε
  simpa only [rescaledGermRelation_fiber G p ε r g hgraph hr hrε] using
    h (Sum.elim p (fun _ => r))

/-- The source's ambient membership is essential: arbitrary intersections of
cell closures are not permitted as attachment points. The exact constructed
curve is retained, and the format constants precede all fiber data. -/
theorem published_curveGermFamily_initialSegment_paths
    (hQE : PublishedRealSemialgebraicity) {ρ κ : Type} [Finite ρ] [Finite κ]
    (G : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ)) (hG : HasPolynomialSignDescription G) :
    ∃ sPath dPath : ℕ, ∀ (p : ρ → ℝ) (ε r : ℝ) (g : ℝ → κ → ℝ)
      (C S : Set (κ → ℝ)),
      projectionFiber G p = curveGermGraph ε g → 0 < r → r < ε →
      ContinuousOn g (Ico (0 : ℝ) ε) → MapsTo g (Ioo (0 : ℝ) ε) C →
      g 0 ∈ S → C ⊆ S →
      ∃ γ : SemialgebraicUnitPath S (g 0) (g r),
        γ.toFun = curveInitialSegment g r ∧ g r ∈ C ∧
        ∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ), A.card ≤ sPath ∧
          (∀ q ∈ A, q.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨sPath,dPath,h⟩ := published_curveGermFamily_initialSegment_format hQE G hG
  refine ⟨sPath,dPath,?_⟩
  intro p ε r g C S hgraph hr hrε hc hm h0 hCS
  obtain ⟨A,hcard,hdegree,hA⟩ := h p ε r g hgraph hr.le hrε
  let γ : SemialgebraicUnitPath S (g 0) (g r) :=
    { toFun := curveInitialSegment g r
      continuousOn := curveInitialSegment_continuousOn hc hr.le hrε
      mapsTo := curveInitialSegment_mapsTo_ambient hm hr hrε h0 hCS
      source := curveInitialSegment_source g r
      target := curveInitialSegment_target g r
      semialgebraic := ⟨A,hA⟩ }
  exact ⟨γ,rfl,hm ⟨hr,hrε⟩,A,hcard,hdegree,hA⟩

end PaperI
