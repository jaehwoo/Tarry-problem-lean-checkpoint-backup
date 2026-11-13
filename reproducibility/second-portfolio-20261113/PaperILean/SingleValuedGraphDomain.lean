import PaperILean.PublishedRealAlgebraicAssumptions
import PaperILean.GraphMonotonicityDefinability

/-! The definable unique-output part of an arbitrary scalar relation. The chosen
function has no mathematical assumptions away from this domain. This lets a
fixed family include nonfunctional and empty instances without changing the
local graph hypothesis on a represented interval. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing Classical.propDecidable

/-- The graph holds for exactly the displayed output, with existence included. -/
def uniqueGraphRelation {κ : Type*} (G : Set ((κ ⊕ Unit) → ℝ)) :
    Set ((κ ⊕ Unit) → ℝ) :=
  {v | ∀ z : Unit → ℝ, Sum.elim (v ∘ Sum.inl) z ∈ G ↔ z () = v (Sum.inr ())}

def uniqueGraphDomain {κ : Type*} (G : Set ((κ ⊕ Unit) → ℝ)) : Set (κ → ℝ) :=
  {x | ∃ y : Unit → ℝ, Sum.elim x y ∈ uniqueGraphRelation G}

def uniqueGraphValue {κ : Type*} (G : Set ((κ ⊕ Unit) → ℝ)) (x : κ → ℝ) : ℝ :=
  if h : x ∈ uniqueGraphDomain G then (Classical.choose h) () else 0

theorem uniqueGraphValue_eq {κ : Type*} (G : Set ((κ ⊕ Unit) → ℝ))
    (x : κ → ℝ) (y : ℝ)
    (h : ∀ z : Unit → ℝ, Sum.elim x z ∈ G ↔ z () = y) :
    x ∈ uniqueGraphDomain G ∧ uniqueGraphValue G x = y := by
  have hx : x ∈ uniqueGraphDomain G := ⟨fun _ => y,h⟩
  refine ⟨hx,?_⟩
  rw [uniqueGraphValue,dif_pos hx]
  have hc := Classical.choose_spec hx
  have he := (hc (Classical.choose hx)).mpr rfl
  exact (h (Classical.choose hx)).mp he

theorem uniqueGraphRelation_eq_graph {κ : Type*} (G : Set ((κ ⊕ Unit) → ℝ)) :
    uniqueGraphRelation G = {v | v ∘ Sum.inl ∈ uniqueGraphDomain G ∧
      v (Sum.inr ()) = uniqueGraphValue G (v ∘ Sum.inl)} := by
  ext v
  constructor
  · intro hv
    have h := uniqueGraphValue_eq G (v ∘ Sum.inl) (v (Sum.inr ())) hv
    exact ⟨h.1,h.2.symm⟩
  · rintro ⟨hx,hy⟩
    intro z
    have hc := Classical.choose_spec hx
    have hval : uniqueGraphValue G (v ∘ Sum.inl) = (Classical.choose hx) () := by
      rw [uniqueGraphValue,dif_pos hx]
    simpa only [Function.comp_def,Sum.elim_inl,Sum.elim_inr,← hval,hy] using hc z

theorem uniqueGraphRelation_definable {κ : Type*} [Finite κ]
    {G : Set ((κ ⊕ Unit) → ℝ)} (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (uniqueGraphRelation G) := by
  let e : (κ ⊕ Unit) → ((κ ⊕ Unit) ⊕ Unit) :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr
  have hmem := hG.preimage_comp e
  have heq := realPolynomial_zero_definable
    ((MvPolynomial.X (Sum.inr ()) : MvPolynomial ((κ ⊕ Unit) ⊕ Unit) ℝ) -
    MvPolynomial.X (Sum.inl (Sum.inr ())))
  have hall := realDefinable_forall ((hmem.compl.union heq).inter (heq.compl.union hmem))
  convert hall using 1
  ext v
  have he (z : Unit → ℝ) : Sum.elim v z ∘ e = Sum.elim (v ∘ Sum.inl) z := by
    funext j
    cases j <;> rfl
  simp only [uniqueGraphRelation, mem_setOf_eq, mem_inter_iff,mem_union,
    mem_compl_iff,mem_preimage,MvPolynomial.eval_X,map_sub,sub_eq_zero,he,Sum.elim_inl,Sum.elim_inr]
  apply forall_congr'
  intro z
  tauto

theorem uniqueGraphDomain_definable {κ : Type*} [Finite κ]
    {G : Set ((κ ⊕ Unit) → ℝ)} (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (uniqueGraphDomain G) :=
  realDefinable_exists (uniqueGraphRelation_definable hG)

/-- Reindex parameter, input, output as `(parameter ⊕ Unit) ⊕ Unit`. -/
def scalarGraphAsUnit {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ)) :
    Set (((α ⊕ Unit) ⊕ Unit) → ℝ) :=
  {v | Sum.elim (fun a => v (Sum.inl (Sum.inl a)))
    ![v (Sum.inl (Sum.inr ())),v (Sum.inr ())] ∈ G}

theorem scalarGraphAsUnit_definable {α : Type*}
    {G : Set ((α ⊕ Fin 2) → ℝ)} (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (scalarGraphAsUnit G) := by
  let e : (α ⊕ Fin 2) → ((α ⊕ Unit) ⊕ Unit) := Sum.elim
    (fun a => Sum.inl (Sum.inl a))
    (fun i => if i = 0 then Sum.inl (Sum.inr ()) else Sum.inr ())
  convert hG.preimage_comp e using 1
  ext v
  have he : v ∘ e = Sum.elim (fun a => v (Sum.inl (Sum.inl a)))
      ![v (Sum.inl (Sum.inr ())),v (Sum.inr ())] := by
    funext j
    cases j with
    | inl a => rfl
    | inr i => fin_cases i <;> rfl
  simp only [scalarGraphAsUnit,mem_setOf_eq,mem_preimage,he]

theorem uniqueGraphValue_scalar_eq {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (t y : ℝ)
    (h : ∀ z : ℝ, Sum.elim p ![t,z] ∈ G ↔ z = y) :
    Sum.elim p (fun _ : Unit => t) ∈ uniqueGraphDomain (scalarGraphAsUnit G) ∧
      uniqueGraphValue (scalarGraphAsUnit G) (Sum.elim p (fun _ : Unit => t)) = y := by
  apply uniqueGraphValue_eq
  intro z
  exact h (z ())

end PaperI
