import PaperILean.PublishedNondifferentiabilityBounds
import PaperILean.FiniteExceptionalCuts
import PaperILean.DerivativeSignSubdivision
import PaperILean.ScalarSemialgebraicFrontier108

/-! Construct actual derivative-sign cut sets from nondifferentiability points
and frontiers of the three signed derivative loci. Whole zero-derivative
intervals remain intact. These are differentiable/sign cuts; analyticity is
not inferred. The separate analytic-cut refinement retains that obligation. -/

noncomputable section
namespace PaperI
open Set FirstOrder
open scoped BigOperators
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem derivativeSignOn_of_graph_frontier_avoidance {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b u v : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t)
    (hsub : Ioo u v ⊆ Ioo a b) (hd : ∀ x ∈ Ioo u v, DifferentiableAt ℝ f x)
    (hpos : ∀ x ∈ Ioo u v, x ∉ frontier (scalarProjectionFiber (graphPositiveDerivativeRelation G) p))
    (hzero : ∀ x ∈ Ioo u v, x ∉ frontier (scalarProjectionFiber (graphZeroDerivativeRelation G) p))
    (hneg : ∀ x ∈ Ioo u v, x ∉ frontier (scalarProjectionFiber (graphNegativeDerivativeRelation G) p)) :
    DerivativeSignOn f (Ioo u v) := by
  by_cases huv : u < v
  · obtain ⟨x,hux,hxv⟩ := exists_between huv
    have hx : x ∈ Ioo u v := ⟨hux,hxv⟩
    rcases lt_trichotomy (deriv f x) 0 with hn | hz | hp
    · right; left
      have hmem : x ∈ scalarProjectionFiber (graphNegativeDerivativeRelation G) p :=
        (graphNegativeDerivativeRelation_realize_iff_on_interval G p f a b x hG (hsub hx)).mpr ⟨hd x hx,hn⟩
      have hS := preconnected_subset_of_avoids_frontier_of_mem isPreconnected_Ioo hneg ⟨x,hx,hmem⟩
      intro y hy
      exact ((graphNegativeDerivativeRelation_realize_iff_on_interval G p f a b y hG (hsub hy)).mp
        (hS hy)).2
    · right; right
      have hmem : x ∈ scalarProjectionFiber (graphZeroDerivativeRelation G) p :=
        (graphZeroDerivativeRelation_realize_iff_on_interval G p f a b x hG (hsub hx)).mpr ⟨hd x hx,hz⟩
      have hS := preconnected_subset_of_avoids_frontier_of_mem isPreconnected_Ioo hzero ⟨x,hx,hmem⟩
      intro y hy
      exact ((graphZeroDerivativeRelation_realize_iff_on_interval G p f a b y hG (hsub hy)).mp
        (hS hy)).2
    · left
      have hmem : x ∈ scalarProjectionFiber (graphPositiveDerivativeRelation G) p :=
        (graphPositiveDerivativeRelation_realize_iff_on_interval G p f a b x hG (hsub hx)).mpr ⟨hd x hx,hp⟩
      have hS := preconnected_subset_of_avoids_frontier_of_mem isPreconnected_Ioo hpos ⟨x,hx,hmem⟩
      intro y hy
      exact ((graphPositiveDerivativeRelation_realize_iff_on_interval G p f a b y hG (hsub hy)).mp
        (hS hy)).2
  · left
    intro x hx
    exact (huv (hx.1.trans hx.2)).elim

def derivativeSignExceptionalFamily {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ))
    (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ) : Fin 4 → Set ℝ :=
  ![nondifferentiabilitySet f a b,
    frontier (scalarProjectionFiber (graphPositiveDerivativeRelation G) p),
    frontier (scalarProjectionFiber (graphZeroDerivativeRelation G) p),
    frontier (scalarProjectionFiber (graphNegativeDerivativeRelation G) p)]

theorem exists_derivative_sign_cut_set_of_finite_exceptions {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t)
    (K : Fin 4 → ℕ)
    (hfin : ∀ i, (derivativeSignExceptionalFamily G p f a b i).Finite)
    (hcard : ∀ i, Nat.card (derivativeSignExceptionalFamily G p f a b i) ≤ K i) :
    ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
      C.card ≤ 2 + ∑ i, K i ∧
      ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
        DifferentiableOn ℝ f (Ioo u v) ∧ DerivativeSignOn f (Ioo u v) := by
  obtain ⟨C,ha,hb,hC,hcount,havoid⟩ :=
    exists_interval_cut_set_of_finite_bad_sets (derivativeSignExceptionalFamily G p f a b) K hfin hcard hab
  refine ⟨C,ha,hb,hC,hcount,?_⟩
  intro u hu v hv huv hgap
  have hs : Ioo u v ⊆ Ioo a b := fun x hx =>
    ⟨(hC u hu).1.trans_lt hx.1,hx.2.trans_le (hC v hv).2⟩
  have hd : ∀ x ∈ Ioo u v, DifferentiableAt ℝ f x := by
    intro x hx
    by_contra hn
    exact havoid u hu v hv huv hgap 0 x hx ⟨hs hx,hn⟩
  refine ⟨fun x hx => (hd x hx).differentiableWithinAt,?_⟩
  apply derivativeSignOn_of_graph_frontier_avoidance G p f a b u v hG hs hd
  · exact havoid u hu v hv huv hgap 1
  · exact havoid u hu v hv huv hgap 2
  · exact havoid u hu v hv huv hgap 3

/-- The common cut bound precedes every parameter, represented function and
endpoint. No analytic cut count is assumed or concluded. -/
theorem published_uniform_derivative_sign_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ K : ℕ, ∀ (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧ C.card ≤ K ∧
        ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          DifferentiableOn ℝ f (Ioo u v) ∧ DerivativeSignOn f (Ioo u v) := by
  obtain ⟨NE,hNE⟩ := published_uniform_nondifferentiability_bound hCell hHardt hQE hNash G hG
  obtain ⟨NP,hNP⟩ := published_scalar_fiber_frontier_card_bound hCell hHardt hQE
    (graphPositiveDerivativeRelation G)
    (hQE.finite_sign_description _ (graphPositiveDerivativeRelation_definable hG))
  obtain ⟨NZ,hNZ⟩ := published_scalar_fiber_frontier_card_bound hCell hHardt hQE
    (graphZeroDerivativeRelation G)
    (hQE.finite_sign_description _ (graphZeroDerivativeRelation_definable hG))
  obtain ⟨NN,hNN⟩ := published_scalar_fiber_frontier_card_bound hCell hHardt hQE
    (graphNegativeDerivativeRelation G)
    (hQE.finite_sign_description _ (graphNegativeDerivativeRelation_definable hG))
  let K : Fin 4 → ℕ := ![NE,NP,NZ,NN]
  refine ⟨2 + ∑ i, K i,?_⟩
  intro p f a b hab hrep
  have hE := hNE p f a b hrep
  have hP := hNP p
  have hZ := hNZ p
  have hN := hNN p
  apply exists_derivative_sign_cut_set_of_finite_exceptions G p f a b hab hrep K
  · intro i
    fin_cases i
    · exact hE.1
    · exact hP.1
    · exact hZ.1
    · exact hN.1
  · intro i
    fin_cases i
    · exact hE.2
    · exact hP.2
    · exact hZ.2
    · exact hN.2

end PaperI
