import PaperILean.ScalarFrontierTopology108
import PaperILean.PublishedScalarFiniteFibers
import PaperILean.PolynomialFiberFormat
import PaperILean.GraphDerivativeDefinability

/-! Actual scalar fiber frontiers, with a common finite bound chosen before the
parameter. The qualitative cover, QE, and Hardt inputs retain their separate
roles. No uniform subdivision or analytic conclusion is assumed. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem published_scalar_fiber_frontier_finite
    (hCell : PublishedFiniteConnectedCover) {α : Type}
    (A : Set ((α ⊕ Unit) → ℝ)) (hA : HasPolynomialSignDescription A)
    (p : α → ℝ) : (frontier (scalarProjectionFiber A p)).Finite := by
  obtain ⟨B,hB⟩ := hA
  have hF : HasPolynomialSignDescription (projectionFiber A p) :=
    ⟨specializePolynomialFamily p B, polynomialSignDetermined_projectionFiber p B A hB⟩
  obtain ⟨n,U,hpre,hcover⟩ := hCell.finite_preconnected_cover (projectionFiber A p) hF
  let e : projectionFiber A p → ℝ := fun v => v.val ()
  let V : Fin n → Set ℝ := fun i => e '' U i
  have he : Continuous e := (continuous_apply ()).comp continuous_subtype_val
  have hV (i : Fin n) : IsPreconnected (V i) := (hpre i).image e he.continuousOn
  have hEq : (⋃ i, V i) = scalarProjectionFiber A p := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,v,hv,rfl⟩ := mem_iUnion.mp hx
      exact (projectionFiberUnitEquivScalar A p v).property
    · intro hx
      let v : projectionFiber A p := ⟨fun _ => x,hx⟩
      obtain ⟨i,hi⟩ := hcover v
      exact mem_iUnion.mpr ⟨i,v,hi,rfl⟩
  rw [← hEq]
  exact finite_frontier_finite_preconnected_cover V hV

def scalarClosureRelation {α : Type*} (A : Set ((α ⊕ Unit) → ℝ)) :
    Set ((α ⊕ Unit) → ℝ) :=
  {v | v (Sum.inr ()) ∈ closure (scalarProjectionFiber A (v ∘ Sum.inl))}

def scalarFrontierRelation {α : Type*} (A : Set ((α ⊕ Unit) → ℝ)) :
    Set ((α ⊕ Unit) → ℝ) :=
  {v | v (Sum.inr ()) ∈ frontier (scalarProjectionFiber A (v ∘ Sum.inl))}

theorem scalarClosureRelation_fiber {α : Type*}
    (A : Set ((α ⊕ Unit) → ℝ)) (p : α → ℝ) :
    scalarProjectionFiber (scalarClosureRelation A) p = closure (scalarProjectionFiber A p) := by
  ext x
  rfl

theorem scalarFrontierRelation_fiber {α : Type*}
    (A : Set ((α ⊕ Unit) → ℝ)) (p : α → ℝ) :
    scalarProjectionFiber (scalarFrontierRelation A) p = frontier (scalarProjectionFiber A p) := by
  ext x
  rfl

theorem real_mem_closure_iff_interval {S : Set ℝ} {x : ℝ} :
    x ∈ closure S ↔ ∀ ε : ℝ, 0 < ε → ∃ t ∈ S, x - ε < t ∧ t < x + ε := by
  rw [Metric.mem_closure_iff]
  apply forall_congr'
  intro ε
  apply imp_congr_right
  intro _
  apply exists_congr
  intro t
  rw [Real.dist_eq, abs_lt]
  constructor <;> rintro ⟨ht,h1,h2⟩ <;> refine ⟨ht,?_,?_⟩ <;> linarith

theorem scalarClosureRelation_definable {α : Type*} [Finite α]
    {A : Set ((α ⊕ Unit) → ℝ)}
    (hA : (univ : Set ℝ).Definable Language.ring A) :
    (univ : Set ℝ).Definable Language.ring (scalarClosureRelation A) := by
  let B := α ⊕ Unit
  let E := B ⊕ Unit
  let T := E ⊕ Unit
  let xi : T := Sum.inl (Sum.inl (Sum.inr ()))
  let ei : T := Sum.inl (Sum.inr ())
  let ti : T := Sum.inr ()
  let eA : (α ⊕ Unit) → T := Sum.elim
    (fun a => Sum.inl (Sum.inl (Sum.inl a))) (fun _ => ti)
  have hLeft := realPolynomial_lt_definable
    (MvPolynomial.X xi - MvPolynomial.X ei) (MvPolynomial.X ti)
  have hRight := realPolynomial_lt_definable
    (MvPolynomial.X ti) (MvPolynomial.X xi + MvPolynomial.X ei)
  have hEx := realDefinable_exists ((hA.preimage_comp eA).inter (hLeft.inter hRight))
  have hEps := realPolynomial_lt_definable (0 : MvPolynomial E ℝ)
    (MvPolynomial.X (Sum.inr ()))
  have hAll := realDefinable_forall (hEps.compl.union hEx)
  convert hAll using 1
  ext v
  have heA (ε t : Unit → ℝ) : (Sum.elim (Sum.elim v ε) t ∘ eA) =
      Sum.elim (v ∘ Sum.inl) (fun _ => t ()) := by
    funext a
    rcases a with a | u
    · rfl
    · cases u; rfl
  simp only [scalarClosureRelation, mem_setOf_eq, real_mem_closure_iff_interval,
    mem_compl_iff, mem_union, mem_inter_iff, mem_preimage,
    MvPolynomial.eval_X, map_zero, map_sub, map_add, xi, ei, ti,
    Sum.elim_inl, Sum.elim_inr]
  change (∀ ε : ℝ, 0 < ε → ∃ t : ℝ,
    Sum.elim (v ∘ Sum.inl) (fun _ => t) ∈ A ∧
      v (Sum.inr ()) - ε < t ∧ t < v (Sum.inr ()) + ε) ↔
    ∀ ε : Unit → ℝ, ¬ (0 < ε ()) ∨ ∃ t : Unit → ℝ,
      (Sum.elim (Sum.elim v ε) t ∘ eA) ∈ A ∧
      v (Sum.inr ()) - ε () < t () ∧ t () < v (Sum.inr ()) + ε ()
  simp only [heA, or_iff_not_imp_left, not_not]
  constructor
  · intro h ε hε
    obtain ⟨t,ht,hlo,hhi⟩ := h (ε ()) hε
    exact ⟨fun _ => t,ht,hlo,hhi⟩
  · intro h ε hε
    obtain ⟨t,ht,hlo,hhi⟩ := h (fun _ => ε) hε
    exact ⟨t (),ht,hlo,hhi⟩

theorem scalarFrontierRelation_eq {α : Type*} (A : Set ((α ⊕ Unit) → ℝ)) :
    scalarFrontierRelation A = scalarClosureRelation A ∩ scalarClosureRelation Aᶜ := by
  ext v
  change (_ ∈ frontier _) ↔ (_ ∈ closure _) ∧ (_ ∈ closure _)
  rw [frontier_eq_closure_inter_closure]
  rfl

theorem scalarFrontierRelation_definable {α : Type*} [Finite α]
    {A : Set ((α ⊕ Unit) → ℝ)}
    (hA : (univ : Set ℝ).Definable Language.ring A) :
    (univ : Set ℝ).Definable Language.ring (scalarFrontierRelation A) := by
  rw [scalarFrontierRelation_eq]
  exact (scalarClosureRelation_definable hA).inter
    (scalarClosureRelation_definable hA.compl)

theorem published_scalarFrontierRelation_sign_description
    (hQE : PublishedRealSemialgebraicity) {α : Type} [Finite α]
    {A : Set ((α ⊕ Unit) → ℝ)} (hA : HasPolynomialSignDescription A) :
    HasPolynomialSignDescription (scalarFrontierRelation A) :=
  hQE.finite_sign_description _
    (scalarFrontierRelation_definable (hasPolynomialSignDescription_definable hA))

theorem published_scalar_fiber_frontier_card_bound
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {α : Type} [Finite α]
    (A : Set ((α ⊕ Unit) → ℝ)) (hA : HasPolynomialSignDescription A) :
    ∃ N : ℕ, ∀ p : α → ℝ,
      (frontier (scalarProjectionFiber A p)).Finite ∧
      Nat.card (frontier (scalarProjectionFiber A p)) ≤ N := by
  obtain ⟨N,hN⟩ := published_scalar_finite_fiber_card_bound hCell hHardt hQE
    (scalarFrontierRelation A) (published_scalarFrontierRelation_sign_description hQE hA)
  refine ⟨N,fun p => ?_⟩
  have hf := published_scalar_fiber_frontier_finite hCell A hA p
  refine ⟨hf,?_⟩
  simpa only [scalarFrontierRelation_fiber] using
    hN p (by simpa only [scalarFrontierRelation_fiber] using hf)

end PaperI
