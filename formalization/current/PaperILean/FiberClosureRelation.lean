import PaperILean.JointCurveSelectionRelations

/-! Fiberwise closure freezes the external parameters. It is not the closure
of the total family. Strict coordinate boxes retain a single vector witness,
including empty coordinate types. Pre-strategy: checkpoint_114_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def fiberClosureRelation {ρ κ : Type*} (C : Set ((ρ ⊕ κ) → ℝ)) :
    Set ((ρ ⊕ κ) → ℝ) :=
  {v | v ∘ Sum.inr ∈ closure (projectionFiber C (v ∘ Sum.inl))}

theorem fiberClosureRelation_fiber {ρ κ : Type*}
    (C : Set ((ρ ⊕ κ) → ℝ)) (p : ρ → ℝ) :
    projectionFiber (fiberClosureRelation C) p = closure (projectionFiber C p) := by
  ext a
  rfl

theorem mem_closure_iff_coordinate_boxes {κ : Type*} [Fintype κ]
    (S : Set (κ → ℝ)) (a : κ → ℝ) :
    a ∈ closure S ↔ ∀ r : ℝ, 0 < r → ∃ x ∈ S, ∀ k, |x k - a k| < r := by
  constructor
  · intro ha r hr
    obtain ⟨x,hx,hd⟩ := Metric.mem_closure_iff.mp ha r hr
    refine ⟨x,hx,fun k => ?_⟩
    have hk := (dist_le_pi_dist a x k).trans_lt hd
    simpa only [Real.dist_eq, abs_sub_comm] using hk
  · intro h
    apply Metric.mem_closure_iff.mpr
    intro r hr
    obtain ⟨x,hx,hbox⟩ := h r hr
    refine ⟨x,hx,(dist_pi_lt_iff hr).mpr (fun k => ?_)⟩
    simpa only [Real.dist_eq, abs_sub_comm] using hbox k

theorem fiberClosureRelation_definable {ρ κ : Type} [Finite ρ] [Fintype κ]
    {C : Set ((ρ ⊕ κ) → ℝ)}
    (hC : (univ : Set ℝ).Definable Language.ring C) :
    (univ : Set ℝ).Definable Language.ring (fiberClosureRelation C) := by
  let B := ρ ⊕ κ
  let e : ρ ⊕ κ → (B ⊕ Unit) ⊕ κ :=
    Sum.elim (fun i => Sum.inl (Sum.inl (Sum.inl i))) Sum.inr
  let R : MvPolynomial ((B ⊕ Unit) ⊕ κ) ℝ :=
    MvPolynomial.X (Sum.inl (Sum.inr ()))
  let Q (k : κ) : MvPolynomial ((B ⊕ Unit) ⊕ κ) ℝ :=
    MvPolynomial.X (Sum.inr k) - MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr k)))
  have hbox := realDefinable_finite_all (fun k : κ =>
    (realPolynomial_lt_definable (-R) (Q k)).inter
      (realPolynomial_lt_definable (Q k) R))
  have hex := realDefinable_exists ((hC.preimage_comp e).inter hbox)
  have hpos := realPolynomial_lt_definable (0 : MvPolynomial (B ⊕ Unit) ℝ)
    (MvPolynomial.X (Sum.inr ()))
  have h := realDefinable_forall (hpos.compl.union hex)
  convert h using 1
  ext v
  have he (r : Unit → ℝ) (x : κ → ℝ) :
      Sum.elim (Sum.elim v r) x ∘ e = Sum.elim (v ∘ Sum.inl) x := by
    funext i; cases i <;> rfl
  simp only [mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff, mem_preimage,
    MvPolynomial.eval_X, map_zero, map_sub, map_neg, R, Q, he,
    Sum.elim_inl, Sum.elim_inr]
  change (v ∘ Sum.inr ∈ closure (projectionFiber C (v ∘ Sum.inl))) ↔ _
  rw [mem_closure_iff_coordinate_boxes]
  constructor
  · intro hv r
    by_cases hr : 0 < r ()
    · right
      obtain ⟨x,hx,hb⟩ := hv (r ()) hr
      exact ⟨x,by simpa only [he, projectionFiber, mem_setOf_eq] using hx,
        fun k => abs_lt.mp (hb k)⟩
    · exact Or.inl hr
  · intro hv r hr
    rcases hv (fun _ => r) with hbad | ⟨x,hx,hb⟩
    · exact (hbad hr).elim
    · exact ⟨x,by simpa only [he, projectionFiber, mem_setOf_eq] using hx,
        fun k => abs_lt.mpr (hb k)⟩

theorem published_fiberClosureRelation_semialgebraic
    (hQE : PublishedRealSemialgebraicity) {ρ κ : Type} [Finite ρ] [Fintype κ]
    {C : Set ((ρ ⊕ κ) → ℝ)} (hC : HasPolynomialSignDescription C) :
    HasPolynomialSignDescription (fiberClosureRelation C) :=
  hQE.finite_sign_description _
    (fiberClosureRelation_definable (hasPolynomialSignDescription_definable hC))

theorem coordinateSectionGraph_definable {ρ κ : Type} [Finite ρ] [Fintype κ]
    {P : Set (ρ → ℝ)} (hP : (univ : Set ℝ).Definable Language.ring P)
    (e : κ → ρ) :
    (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph P (fun p => p ∘ e)) := by
  have heq := realDefinable_finite_all (fun k : κ => realPolynomial_zero_definable
    (MvPolynomial.X (Sum.inl (e k) : ρ ⊕ κ) - MvPolynomial.X (Sum.inr k)))
  convert (hP.preimage_comp Sum.inl).inter heq using 1
  ext v
  simp only [selectedFunctionGraph, mem_setOf_eq, mem_inter_iff, mem_preimage,
    map_sub, MvPolynomial.eval_X, sub_eq_zero, funext_iff, Function.comp_apply]
  rfl

end PaperI
