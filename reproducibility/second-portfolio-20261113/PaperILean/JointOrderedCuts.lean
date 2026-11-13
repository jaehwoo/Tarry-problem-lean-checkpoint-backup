import PaperILean.JointOriginalScalarCuts
import PaperILean.FiniteOrderedCuts
import PaperILean.CylindricalDefinableChoice

/-! The actual sorted finite cut fibre is selected jointly by the original
CAD selector. All cuts precede arbitrary Borel parameter substitution.
No pointwise-choice measurability premise is added. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def jointPaddedCutRelation {α : Type*} (C : Set ((α ⊕ Unit) → ℝ)) (K : ℕ) :
    Set ((α ⊕ Fin (K+1)) → ℝ) :=
  {v | PaddedUnitCutEnumeration (scalarProjectionFiber C (v ∘ Sum.inl)) (v ∘ Sum.inr)}

theorem jointPaddedCutRelation_definable {α : Type} [Finite α]
    {C : Set ((α ⊕ Unit) → ℝ)}
    (hC : (univ : Set ℝ).Definable Language.ring C) (K : ℕ) :
    (univ : Set ℝ).Definable Language.ring (jointPaddedCutRelation C K) := by
  let B := α ⊕ Fin (K+1)
  let E := B ⊕ Unit
  let ei : α ⊕ Unit → E := Sum.elim (fun a => Sum.inl (Sum.inl a)) Sum.inr
  have hmem := realDefinable_finite_all (fun j : Fin (K+1) =>
    hC.preimage_comp (Sum.map id (fun _ : Unit => j)))
  have hz := realPolynomial_zero_definable (MvPolynomial.X (Sum.inr (0 : Fin (K+1)) : B))
  have hl := realPolynomial_zero_definable
    (MvPolynomial.X (Sum.inr (Fin.last K) : B)-1)
  have hstep := realDefinable_finite_all (fun j : Fin K =>
    (realPolynomial_lt_definable (MvPolynomial.X (Sum.inr j.castSucc : B))
      (MvPolynomial.X (Sum.inr j.succ))).union
    ((realPolynomial_zero_definable (MvPolynomial.X (Sum.inr j.castSucc : B)-1)).inter
      (realPolynomial_zero_definable (MvPolynomial.X (Sum.inr j.succ : B)-1))))
  have hEq (j : Fin (K+1)) := realPolynomial_zero_definable
    (MvPolynomial.X (Sum.inl (Sum.inr j) : E)-MvPolynomial.X (Sum.inr ()))
  have hAny := (realDefinable_finite_all (fun j => (hEq j).compl)).compl
  have hAll := realDefinable_forall ((hC.preimage_comp ei).compl.union hAny)
  have hcover : (univ : Set ℝ).Definable Language.ring
      {v : B → ℝ | ∀ x ∈ scalarProjectionFiber C (v ∘ Sum.inl),
        ∃ j : Fin (K+1), v (Sum.inr j)=x} := by
    convert hAll using 1
    ext v
    have he (x : Unit → ℝ) : Sum.elim v x ∘ ei =
        Sum.elim (v ∘ Sum.inl) (fun _ => x ()) := by
      funext i
      rcases i with i | ⟨⟩ <;> rfl
    simp only [mem_setOf_eq,mem_union,mem_compl_iff,mem_preimage,
      he,not_forall,not_not,map_sub,MvPolynomial.eval_X,Sum.elim_inl,Sum.elim_inr,sub_eq_zero]
    constructor
    · intro h x
      by_cases hx : x () ∈ scalarProjectionFiber C (v ∘ Sum.inl)
      · exact Or.inr (h (x ()) hx)
      · exact Or.inl hx
    · intro h x hx
      exact (h (fun _ => x)).resolve_left (not_not.mpr hx)
  convert hmem.inter (hz.inter (hl.inter (hstep.inter hcover))) using 1
  ext v
  simp only [jointPaddedCutRelation,PaddedUnitCutEnumeration,mem_setOf_eq,
    mem_inter_iff,mem_union,mem_preimage,map_sub,map_one,MvPolynomial.eval_X,sub_eq_zero]
  have he (j : Fin (K+1)) : Sum.elim (v ∘ Sum.inl) (fun _ => v (Sum.inr j)) =
      v ∘ Sum.map id (fun _ : Unit => j) := by
    funext i
    rcases i with i | ⟨⟩ <;> rfl
  simp only [scalarProjectionFiber,mem_setOf_eq,Function.comp_apply,he]
  rfl

/-- Fixed finite cut relation, fixed budget, then a joint semialgebraic
enumeration and its Borel realization. The cuts themselves are not replaced. -/
theorem published_joint_padded_unit_cuts
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {α : Type} [Finite α] (C : Set ((α ⊕ Unit) → ℝ))
    (hC : HasPolynomialSignDescription C) (K : ℕ)
    (hf : ∀ p, (scalarProjectionFiber C p).Finite)
    (hcard : ∀ p, Nat.card (scalarProjectionFiber C p) ≤ K+1)
    (h0 : ∀ p, 0 ∈ scalarProjectionFiber C p)
    (h1 : ∀ p, 1 ∈ scalarProjectionFiber C p)
    (hsub : ∀ p, scalarProjectionFiber C p ⊆ Icc (0:ℝ) 1) :
    ∃ t : (α → ℝ) → Fin (K+1) → ℝ,
      HasPolynomialSignDescription (selectedFunctionGraph univ t) ∧ Measurable t ∧
      ∀ p, PaddedUnitCutEnumeration (scalarProjectionFiber C p) (t p) := by
  classical
  letI := Fintype.ofFinite α
  have hR := hQE.finite_sign_description _
    (jointPaddedCutRelation_definable (hasPolynomialSignDescription_definable hC) K)
  obtain ⟨t,ht,hm⟩ := published_cylindrical_selector hCAD hQE
    (univ : Set (α → ℝ)) (jointPaddedCutRelation C K)
    ⟨∅,polynomialSignDetermined_univ⟩ hR (fun p _ =>
      exists_paddedUnitCutEnumeration (hf p) (h0 p) (h1 p) (hsub p) K (hcard p))
  have htmeas := published_measurable_selected_function hQE hHardt univ t
    (hasPolynomialSignDescription_definable ht)
  have hi : Measurable (fun p : α → ℝ => (⟨p,mem_univ p⟩ : (univ : Set (α → ℝ)))) :=
    measurable_id.subtype_mk
  exact ⟨t,ht,htmeas.comp hi,fun p => hm p (mem_univ p)⟩

def OrderedUnitCutFamily {α : Type*} (C : Set ((α ⊕ Unit) → ℝ)) (K : ℕ)
    (n : (α → ℝ) → ℕ) (t : (α → ℝ) → ℕ → ℝ) : Prop :=
  ∀ p, 0<n p ∧ n p≤K ∧ t p 0=0 ∧ t p (n p)=1 ∧
    MonotoneOn (t p) (Icc 0 (n p)) ∧ (∀ j≥n p, t p j=1) ∧
    ∀ j<n p, t p j ∈ scalarProjectionFiber C p ∧
      t p (j+1) ∈ scalarProjectionFiber C p ∧ t p j<t p (j+1) ∧
      ∀ c ∈ scalarProjectionFiber C p, c ∉ Ioo (t p j) (t p (j+1))

theorem published_joint_ordered_unit_cuts
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {α : Type} [Finite α] (C : Set ((α ⊕ Unit) → ℝ))
    (hC : HasPolynomialSignDescription C) (K : ℕ)
    (hf : ∀ p, (scalarProjectionFiber C p).Finite)
    (hcard : ∀ p, Nat.card (scalarProjectionFiber C p) ≤ K+1)
    (h0 : ∀ p, 0 ∈ scalarProjectionFiber C p)
    (h1 : ∀ p, 1 ∈ scalarProjectionFiber C p)
    (hsub : ∀ p, scalarProjectionFiber C p ⊆ Icc (0:ℝ) 1) :
    ∃ (n : (α → ℝ) → ℕ) (t : (α → ℝ) → ℕ → ℝ),
      Measurable n ∧ (∀ j, Measurable (fun p => t p j)) ∧ OrderedUnitCutFamily C K n t := by
  obtain ⟨T,hgraph,hT,hEnum⟩ := published_joint_padded_unit_cuts
    hCAD hQE hHardt C hC K hf hcard h0 h1 hsub
  exact ⟨fun p => activeCutCount (T p) (hEnum p).2.2.1,
    fun p => paddedCutSequence (T p),
    measurable_activeCutCount T hT (fun p => (hEnum p).2.2.1),
    measurable_paddedCutSequence T hT,
    fun p => (hEnum p).active_partition (hsub p)⟩

/-- First application to the original analytic/sign construction: one joint
cut relation, one uniform budget, and actual Borel sorted cuts and active count.
This asserts no graph direction or prepared interval selection. -/
theorem published_joint_original_scalar_subdivision
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hPiece : PublishedPiecewiseNashExtensions)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ (C : Set ((α ⊕ Unit) → ℝ)) (K : ℕ)
      (n : (α → ℝ) → ℕ) (t : (α → ℝ) → ℕ → ℝ),
      HasPolynomialSignDescription C ∧ JointOriginalScalarCutFamily G C K ∧
      Measurable n ∧ (∀ j, Measurable (fun p => t p j)) ∧ OrderedUnitCutFamily C K n t := by
  obtain ⟨C,K,hC,hcuts⟩ := published_joint_original_scalar_cut_family hCell hHardt hQE hPiece G hG
  obtain ⟨n,t,hn,ht,hord⟩ := published_joint_ordered_unit_cuts hCAD hQE hHardt C hC K
    (fun p => (hcuts p).1) (fun p => (hcuts p).2.1.trans (Nat.le_succ K))
    (fun p => (hcuts p).2.2.1) (fun p => (hcuts p).2.2.2.1) (fun p => (hcuts p).2.2.2.2.1)
  exact ⟨C,K,n,t,hC,hcuts,hn,ht,hord⟩

end PaperI
