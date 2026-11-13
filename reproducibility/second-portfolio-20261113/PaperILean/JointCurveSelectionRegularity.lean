import PaperILean.JointCurveSelectionRelations
import PaperILean.PublishedScalarAnalyticity

/-! A jointly definable relation of good radii. Pointwise finite exceptional
sets prove only that its fibers are nonempty; a second joint choice chooses
the radii. Differentiability is a sufficient interior-continuity test, not an
additional hypothesis on the cells or on the initial selector. -/

noncomputable section
namespace PaperI
open Set FirstOrder Filter
open scoped Topology
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def jointCoordinateGraph {ρ κ : Type*}
    (H : Set (((ρ ⊕ Unit) ⊕ κ) → ℝ)) (k : κ) : Set ((ρ ⊕ Fin 2) → ℝ) :=
  {v | ∃ x : κ → ℝ,
    Sum.elim (Sum.elim (v ∘ Sum.inl) (fun _ => v (Sum.inr 0))) x ∈ H ∧
      x k = v (Sum.inr 1)}

theorem jointCoordinateGraph_definable {ρ κ : Type} [Finite ρ] [Finite κ]
    {H : Set (((ρ ⊕ Unit) ⊕ κ) → ℝ)}
    (hH : (univ : Set ℝ).Definable Language.ring H) (k : κ) :
    (univ : Set ℝ).Definable Language.ring (jointCoordinateGraph H k) := by
  let e : (ρ ⊕ Unit) ⊕ κ → (ρ ⊕ Fin 2) ⊕ κ :=
    Sum.elim (Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun _ => Sum.inl (Sum.inr 0))) Sum.inr
  have heq := realPolynomial_zero_definable
    (MvPolynomial.X (Sum.inr k : (ρ ⊕ Fin 2) ⊕ κ) - MvPolynomial.X (Sum.inl (Sum.inr 1)))
  have h := realDefinable_exists ((hH.preimage_comp e).inter heq)
  convert h using 1
  ext v
  have he (x : κ → ℝ) : Sum.elim v x ∘ e =
      Sum.elim (Sum.elim (v ∘ Sum.inl) (fun _ => v (Sum.inr 0))) x := by
    funext i
    rcases i with (i | ⟨⟩) | k <;> rfl
  simp only [jointCoordinateGraph, mem_setOf_eq, mem_inter_iff, mem_preimage,
    he, map_sub, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr, sub_eq_zero]

theorem jointCoordinateGraph_positive_realize {ρ κ : Type*}
    (P : Set (ρ → ℝ)) (f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ)
    {p : ρ → ℝ} (hp : p ∈ P) {t : ℝ} (ht : 0 < t) (y : ℝ) (k : κ) :
    Sum.elim p ![t,y] ∈ jointCoordinateGraph
      (selectedFunctionGraph (positiveTimeDomain P) f) k ↔
      y = f (Sum.elim p (fun _ => t)) k := by
  change (∃ x : κ → ℝ, ((p ∈ P ∧ 0 < t) ∧ f (Sum.elim p (fun _ => t)) = x) ∧ x k = y) ↔ _
  constructor
  · rintro ⟨x,⟨_,hx⟩,hy⟩
    exact hy.symm.trans (congrFun hx.symm k)
  · intro hy
    exact ⟨f _,⟨⟨hp,ht⟩,rfl⟩,hy.symm⟩

theorem jointCoordinateGraph_open_fiber_sign
    (hQE : PublishedRealSemialgebraicity) {ρ κ : Type} [Finite ρ] [Finite κ]
    (P : Set (ρ → ℝ)) (f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ)
    (hf : HasPolynomialSignDescription (selectedFunctionGraph (positiveTimeDomain P) f))
    {p : ρ → ℝ} (hp : p ∈ P) (k : κ) :
    HasPolynomialSignDescription
      (openScalarGraph (fun t => f (Sum.elim p (fun _ => t)) k) 0 1) := by
  let G := jointCoordinateGraph (selectedFunctionGraph (positiveTimeDomain P) f) k
  obtain ⟨A,hA⟩ := hQE.finite_sign_description G
    (jointCoordinateGraph_definable (hasPolynomialSignDescription_definable hf) k)
  have hF := hasPolynomialSignDescription_definable
    (⟨specializePolynomialFamily p A, polynomialSignDetermined_projectionFiber p A G hA⟩ :
      HasPolynomialSignDescription (projectionFiber G p))
  have h0 := realPolynomial_lt_definable (0 : MvPolynomial (Fin 2) ℝ) (MvPolynomial.X 0)
  have h1 := realPolynomial_lt_definable (MvPolynomial.X (0 : Fin 2)) 1
  apply hQE.finite_sign_description
  convert (h0.inter h1).inter hF using 1
  ext v
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  simp only [openScalarGraph, mem_setOf_eq, mem_inter_iff, map_zero, map_one, MvPolynomial.eval_X]
  constructor
  · rintro ⟨h0,h1,hy⟩
    refine ⟨⟨h0,h1⟩,?_⟩
    change Sum.elim p v ∈ G
    rw [hv]
    exact (jointCoordinateGraph_positive_realize P f hp h0 (v 1) k).mpr hy
  · rintro ⟨⟨h0,h1⟩,hy⟩
    refine ⟨h0,h1,?_⟩
    apply (jointCoordinateGraph_positive_realize P f hp h0 (v 1) k).mp
    change Sum.elim p v ∈ G at hy
    simpa only [← hv] using hy

theorem finite_positive_set_has_initial_gap (E : Finset ℝ)
    (hE : ∀ x ∈ E, 0 < x) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ t ∈ Ioo (0 : ℝ) r, t ∉ E := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨1/2, by norm_num, by norm_num, by simp⟩
  | @insert x E hx ih =>
    obtain ⟨r,hr,hr1,hgap⟩ := ih (fun y hy => hE y (Finset.mem_insert_of_mem hy))
    refine ⟨min r x, lt_min hr (hE x (Finset.mem_insert_self _ _)),
      lt_of_le_of_lt (min_le_left _ _) hr1, ?_⟩
    intro t ht hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem
    · exact (not_lt_of_ge (min_le_right r t)) ht.2
    · exact hgap t ⟨ht.1,ht.2.trans_le (min_le_left _ _)⟩ hmem

def jointDifferentiableRadiusRelation {ρ κ : Type*} (P : Set (ρ → ℝ))
    (H : Set (((ρ ⊕ Unit) ⊕ κ) → ℝ)) : Set ((ρ ⊕ Unit) → ℝ) :=
  {v | v ∘ Sum.inl ∈ P ∧ 0 < v (Sum.inr ()) ∧ v (Sum.inr ()) < 1 ∧
    ∀ t : Unit → ℝ, 0 < t () → t () < v (Sum.inr ()) → ∀ k : κ,
      Sum.elim (v ∘ Sum.inl) t ∈ graphDerivativeExistsRelation (jointCoordinateGraph H k)}

theorem jointDifferentiableRadiusRelation_definable {ρ κ : Type} [Finite ρ] [Fintype κ]
    {P : Set (ρ → ℝ)} {H : Set (((ρ ⊕ Unit) ⊕ κ) → ℝ)}
    (hP : (univ : Set ℝ).Definable Language.ring P)
    (hH : (univ : Set ℝ).Definable Language.ring H) :
    (univ : Set ℝ).Definable Language.ring (jointDifferentiableRadiusRelation P H) := by
  let e : ρ ⊕ Unit → (ρ ⊕ Unit) ⊕ Unit :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr
  have hall := realDefinable_finite_all (fun k : κ =>
    (graphDerivativeExistsRelation_definable (jointCoordinateGraph_definable hH k)).preimage_comp e)
  have ht0 := realPolynomial_lt_definable (0 : MvPolynomial ((ρ ⊕ Unit) ⊕ Unit) ℝ)
    (MvPolynomial.X (Sum.inr ()))
  have htr := realCoordinate_lt_definable (Sum.inr () : (ρ ⊕ Unit) ⊕ Unit)
    (Sum.inl (Sum.inr ()))
  have hforall := realDefinable_forall ((ht0.inter htr).compl.union hall)
  have hr0 := realPolynomial_lt_definable (0 : MvPolynomial (ρ ⊕ Unit) ℝ)
    (MvPolynomial.X (Sum.inr ()))
  have hr1 := realPolynomial_lt_definable (MvPolynomial.X (Sum.inr () : ρ ⊕ Unit)) 1
  convert (hP.preimage_comp Sum.inl).inter (hr0.inter (hr1.inter hforall)) using 1
  ext v
  have he (t : Unit → ℝ) : Sum.elim v t ∘ e = Sum.elim (v ∘ Sum.inl) t := by
    funext i; cases i <;> rfl
  simp only [jointDifferentiableRadiusRelation, mem_setOf_eq, mem_inter_iff,
    mem_preimage, mem_compl_iff, mem_union, MvPolynomial.eval_X, map_zero, map_one,
    Sum.elim_inl, Sum.elim_inr, he]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply forall_congr'; intro t
  tauto

theorem jointCoordinateGraph_derivative_iff {ρ κ : Type*}
    (P : Set (ρ → ℝ)) (f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ)
    {p : ρ → ℝ} (hp : p ∈ P) {t : ℝ} (ht : 0 < t) (k : κ) :
    Sum.elim p (fun _ => t) ∈ graphDerivativeExistsRelation
      (jointCoordinateGraph (selectedFunctionGraph (positiveTimeDomain P) f) k) ↔
      DifferentiableAt ℝ (fun u => f (Sum.elim p (fun _ => u)) k) t := by
  let G := jointCoordinateGraph (selectedFunctionGraph (positiveTimeDomain P) f) k
  have hlocal : ∀ᶠ u in 𝓝 t, ∀ y : ℝ, Sum.elim p ![u,y] ∈ G ↔
      y = f (Sum.elim p (fun _ => u)) k := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact fun y => jointCoordinateGraph_positive_realize P f hp hu y k
  constructor
  · rintro ⟨m,hm,_⟩
    exact ((graphDerivativeRelation_realize_iff_of_local_graph G p _ t (m ()) hlocal).mp hm).differentiableAt
  · intro hd
    exact ⟨fun _ => deriv (fun u => f (Sum.elim p (fun _ => u)) k) t,
      (graphDerivativeRelation_realize_iff_of_local_graph G p _ t _ hlocal).mpr hd.hasDerivAt,
      mem_univ _⟩

theorem published_joint_good_radius_domain
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (P : Set (ρ → ℝ)) (f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ)
    (hf : HasPolynomialSignDescription (selectedFunctionGraph (positiveTimeDomain P) f)) :
    projectionDomain (jointDifferentiableRadiusRelation P
      (selectedFunctionGraph (positiveTimeDomain P) f)) = P := by
  ext p
  constructor
  · rintro ⟨r,hp,_,_,_⟩; exact hp
  · intro hp
    obtain ⟨E,hE,hA⟩ := published_finite_family_analytic_exceptions hNash
      (fun k t => f (Sum.elim p (fun _ => t)) k) 0 1 zero_lt_one
      (jointCoordinateGraph_open_fiber_sign hQE P f hf hp)
    obtain ⟨r,hr,hr1,hgap⟩ := finite_positive_set_has_initial_gap E (fun x hx => (hE x hx).1)
    refine ⟨fun _ => r,hp,hr,hr1,fun t ht htr k => ?_⟩
    apply (jointCoordinateGraph_derivative_iff P f hp ht k).mpr
    exact (hA (t ()) ⟨ht,htr.trans hr1⟩ (hgap (t ()) ⟨ht,htr⟩) k).differentiableAt

/-- The chosen radius is jointly semialgebraic; arbitrary pointwise choices
of the exceptional sets do not enter the chosen graph. -/
theorem published_joint_differentiable_radius
    (hChoice : PublishedSemialgebraicDefinableChoice)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (P : Set (ρ → ℝ)) (f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ)
    (hP : HasPolynomialSignDescription P)
    (hf : HasPolynomialSignDescription (selectedFunctionGraph (positiveTimeDomain P) f)) :
    ∃ ε : (ρ → ℝ) → ℝ,
      HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)) ∧
      ∀ p ∈ P, 0 < ε p ∧ ε p < 1 ∧
        ∀ t ∈ Ioo (0 : ℝ) (ε p), ∀ k,
          DifferentiableAt ℝ (fun u => f (Sum.elim p (fun _ => u)) k) t := by
  let H := selectedFunctionGraph (positiveTimeDomain P) f
  obtain ⟨e,he,hm⟩ := hChoice.section_exists (jointDifferentiableRadiusRelation P H)
    (hQE.finite_sign_description _ (jointDifferentiableRadiusRelation_definable
      (hasPolynomialSignDescription_definable hP) (hasPolynomialSignDescription_definable hf)))
  rw [published_joint_good_radius_domain hQE hNash P f hf] at he hm
  refine ⟨fun p => e p (),?_,?_⟩
  · convert he using 1
  · intro p hp
    have h := hm p hp
    refine ⟨h.2.1,h.2.2.1,fun t ht k => ?_⟩
    exact (jointCoordinateGraph_derivative_iff P f hp ht.1 k).mp
      (h.2.2.2 (fun _ => t) ht.1 ht.2 k)

end PaperI
