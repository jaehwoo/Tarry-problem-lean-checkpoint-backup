import PaperILean.ClosedMonotoneArc

/-! The closed extension's graph is precisely the closure of the open graph.
For joint families, the closure is fiberwise in time AND output coordinates,
with external parameters frozen. This yields a uniform format prerequisite,
not a uniform number of boundary arcs. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def parametrizedArcGraph {κ : Type*} (γ : ℝ → κ → ℝ) (S : Set ℝ) :
    Set ((Unit ⊕ κ) → ℝ) :=
  (fun t => Sum.elim (fun _ : Unit => t) (γ t)) '' S

theorem mem_parametrizedArcGraph {κ : Type*} (γ : ℝ → κ → ℝ) (S : Set ℝ)
    (v : (Unit ⊕ κ) → ℝ) :
    v ∈ parametrizedArcGraph γ S ↔
      v (Sum.inl ()) ∈ S ∧ ∀ i, v (Sum.inr i) = γ (v (Sum.inl ())) i := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ht, fun _ => rfl⟩
  · rintro ⟨ht, hv⟩
    refine ⟨v (Sum.inl ()), ht, ?_⟩
    funext i
    rcases i with u | i
    · cases u; rfl
    · exact (hv i).symm

theorem closed_interval_extension_graph_eq_closure {κ : Type*}
    {γ Γ : ℝ → κ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn Γ (Icc a b)) (he : EqOn Γ γ (Ioo a b)) :
    parametrizedArcGraph Γ (Icc a b) = closure (parametrizedArcGraph γ (Ioo a b)) := by
  apply closed_interval_extension_image_eq_closure hab
  · apply continuousOn_pi.mpr
    intro i
    rcases i with u | i
    · exact continuousOn_id
    · exact (continuous_apply i).comp_continuousOn hc
  · intro t ht
    funext i
    rcases i with u | i
    · rfl
    · exact congrFun (he ht) i

theorem closedMonotoneArc_graph_eq_closure {κ : Type*}
    {γ : ℝ → κ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn γ (Ioo a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Ioo a b) ∨
      AntitoneOn (fun t => γ t i) (Ioo a b))
    (hlo : ∀ i, BddBelow ((fun t => γ t i) '' Ioo a b))
    (hhi : ∀ i, BddAbove ((fun t => γ t i) '' Ioo a b)) :
    parametrizedArcGraph (closedMonotoneArc γ a b) (Icc a b) =
      closure (parametrizedArcGraph γ (Ioo a b)) :=
  closed_interval_extension_graph_eq_closure hab
    (closedMonotoneArc_continuousOn hab hc hm hlo hhi)
    (fun _ ht => closedMonotoneArc_eq hc ht)

/-- The format bounds precede p and every endpoint/continuity/monotonicity
verification. All coefficients remain in the fixed joint graph C. -/
theorem published_closedMonotoneArc_family_uniform_format
    (hQE : PublishedRealSemialgebraicity) {ρ κ : Type} [Finite ρ] [Fintype κ]
    (C : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ))
    (hC : (univ : Set ℝ).Definable Language.ring C)
    (γ : (ρ → ℝ) → ℝ → κ → ℝ) (a b : (ρ → ℝ) → ℝ)
    (hGraph : ∀ p, projectionFiber C p = parametrizedArcGraph (γ p) (Ioo (a p) (b p))) :
    ∃ s D : ℕ, ∀ p : ρ → ℝ, a p < b p →
      ContinuousOn (γ p) (Ioo (a p) (b p)) →
      (∀ i, MonotoneOn (fun t => γ p t i) (Ioo (a p) (b p)) ∨
        AntitoneOn (fun t => γ p t i) (Ioo (a p) (b p))) →
      (∀ i, BddBelow ((fun t => γ p t i) '' Ioo (a p) (b p))) →
      (∀ i, BddAbove ((fun t => γ p t i) '' Ioo (a p) (b p))) →
      ∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ), A.card ≤ s ∧
        (∀ q ∈ A, q.totalDegree ≤ D) ∧ PolynomialSignDetermined A
          (parametrizedArcGraph (closedMonotoneArc (γ p) (a p) (b p)) (Icc (a p) (b p))) := by
  obtain ⟨s, D, h⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format
    (hQE.finite_sign_description _ (fiberClosureRelation_definable hC))
  refine ⟨s, D, ?_⟩
  intro p hab hc hm hlo hhi
  simpa only [fiberClosureRelation_fiber, hGraph,
    closedMonotoneArc_graph_eq_closure hab hc hm hlo hhi] using h p

end PaperI
