import PaperILean.PublishedDefinableChoice
import PaperILean.CurveGermSemialgebraic
import PaperILean.GraphDerivativeLoci

/-! The nearby-point relation retains one parameter and one whole vector
witness. Strict boxes include singleton and zero-dimensional fibers. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def positiveTimeDomain {ρ : Type*} (P : Set (ρ → ℝ)) : Set ((ρ ⊕ Unit) → ℝ) :=
  {v | v ∘ Sum.inl ∈ P ∧ 0 < v (Sum.inr ())}

def nearbyPointRelation {ρ κ : Type*} (P : Set (ρ → ℝ))
    (C : Set ((ρ ⊕ κ) → ℝ)) (a : (ρ → ℝ) → κ → ℝ) :
    Set (((ρ ⊕ Unit) ⊕ κ) → ℝ) :=
  {v | (fun i => v (Sum.inl (Sum.inl i))) ∈ P ∧
    0 < v (Sum.inl (Sum.inr ())) ∧
    Sum.elim (fun i => v (Sum.inl (Sum.inl i))) (v ∘ Sum.inr) ∈ C ∧
    ∀ k, |v (Sum.inr k) - a (fun i => v (Sum.inl (Sum.inl i))) k| <
      v (Sum.inl (Sum.inr ()))}

theorem nearbyPointRelation_definable {ρ κ : Type} [Finite ρ] [Fintype κ]
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ)) (a : (ρ → ℝ) → κ → ℝ)
    (hC : (univ : Set ℝ).Definable Language.ring C)
    (ha : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P a)) :
    (univ : Set ℝ).Definable Language.ring (nearbyPointRelation P C a) := by
  let B := (ρ ⊕ Unit) ⊕ κ
  let eA : ρ ⊕ κ → B ⊕ κ :=
    Sum.elim (fun i => Sum.inl (Sum.inl (Sum.inl i))) Sum.inr
  let eC : ρ ⊕ κ → B ⊕ κ :=
    Sum.elim (fun i => Sum.inl (Sum.inl (Sum.inl i))) (fun k => Sum.inl (Sum.inr k))
  let ti : B ⊕ κ := Sum.inl (Sum.inl (Sum.inr ()))
  have hpos := realPolynomial_lt_definable (0 : MvPolynomial (B ⊕ κ) ℝ)
    (MvPolynomial.X ti)
  have hbox := realDefinable_finite_all (fun k : κ =>
    (realPolynomial_lt_definable (-MvPolynomial.X ti)
      (MvPolynomial.X (Sum.inl (Sum.inr k)) - MvPolynomial.X (Sum.inr k))).inter
    (realPolynomial_lt_definable
      (MvPolynomial.X (Sum.inl (Sum.inr k)) - MvPolynomial.X (Sum.inr k)) (MvPolynomial.X ti)))
  have h := realDefinable_exists (((ha.preimage_comp eA).inter hpos).inter
    ((hC.preimage_comp eC).inter hbox))
  convert h using 1
  ext v
  have heA (w : κ → ℝ) : Sum.elim v w ∘ eA =
      Sum.elim (fun i => v (Sum.inl (Sum.inl i))) w := by
    funext i; cases i <;> rfl
  have heC (w : κ → ℝ) : Sum.elim v w ∘ eC =
      Sum.elim (fun i => v (Sum.inl (Sum.inl i))) (v ∘ Sum.inr) := by
    funext i; cases i <;> rfl
  simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, heA, heC,
    selectedFunctionGraph, MvPolynomial.eval_X, map_zero, map_sub, map_neg,
    ti, Sum.elim_inl, Sum.elim_inr]
  change ( _ ∧ _ ∧ _ ∧ ∀ k, |v (Sum.inr k) - a (fun i => v (Sum.inl (Sum.inl i))) k| <
      v (Sum.inl (Sum.inr ()))) ↔
    ∃ w : κ → ℝ, ((_ ∧ a (fun i => v (Sum.inl (Sum.inl i))) = w) ∧ _) ∧
      (_ ∧ ∀ k, -v (Sum.inl (Sum.inr ())) < v (Sum.inr k) - w k ∧
        v (Sum.inr k) - w k < v (Sum.inl (Sum.inr ())))
  simp only [heA, heC]
  constructor
  · rintro ⟨hp,ht,hc,hb⟩
    exact ⟨a _,⟨⟨hp,rfl⟩,ht⟩,hc,fun k => abs_lt.mp (hb k)⟩
  · rintro ⟨w,⟨⟨hp,hw⟩,ht⟩,hc,hb⟩
    subst w
    exact ⟨hp,ht,hc,fun k => abs_lt.mpr (hb k)⟩

theorem nearbyPointRelation_domain {ρ κ : Type} [Fintype κ]
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ)) (a : (ρ → ℝ) → κ → ℝ)
    (hcl : ∀ p ∈ P, a p ∈ closure (projectionFiber C p)) :
    projectionDomain (nearbyPointRelation P C a) = positiveTimeDomain P := by
  ext v
  constructor
  · rintro ⟨x,hp,ht,_,_⟩
    exact ⟨hp,ht⟩
  · rintro ⟨hp,ht⟩
    obtain ⟨x,hx,hclose⟩ := Metric.mem_closure_iff.mp (hcl (v ∘ Sum.inl) hp) _ ht
    refine ⟨x,hp,ht,hx,fun k => ?_⟩
    have hk := (dist_le_pi_dist (a (v ∘ Sum.inl)) x k).trans_lt hclose
    simpa only [Real.dist_eq, abs_sub_comm] using hk

/-- A semialgebraic graph on the actual positive-time domain, selected jointly. -/
theorem published_joint_nearby_selector
    (hChoice : PublishedSemialgebraicDefinableChoice) (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ)) (a : (ρ → ℝ) → κ → ℝ)
    (hC : HasPolynomialSignDescription C)
    (ha : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hcl : ∀ p ∈ P, a p ∈ closure (projectionFiber C p)) :
    ∃ f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ,
      HasPolynomialSignDescription (selectedFunctionGraph (positiveTimeDomain P) f) ∧
      ∀ p ∈ P, ∀ t : ℝ, 0 < t →
        f (Sum.elim p (fun _ => t)) ∈ projectionFiber C p ∧
        ∀ k, |f (Sum.elim p (fun _ => t)) k - a p k| < t := by
  obtain ⟨f,hf,hm⟩ := hChoice.section_exists (nearbyPointRelation P C a)
    (hQE.finite_sign_description _ (nearbyPointRelation_definable P C a
      (hasPolynomialSignDescription_definable hC) (hasPolynomialSignDescription_definable ha)))
  rw [nearbyPointRelation_domain P C a hcl] at hf hm
  refine ⟨f,hf,fun p hp t ht => ?_⟩
  exact (hm (Sum.elim p (fun _ => t)) ⟨hp,ht⟩).2.2

end PaperI
