import PaperILean.FiberClosureRelation

/-! Definable graph operations for the literal cylindrical-section construction.
All functions are restricted to their stated domains. These are local proofs,
not additional published inputs. Prerequisite: cad117_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem cad_selectedGraph_restrict {α β : Type*}
    {U V : Set (α → ℝ)} (hUV : U ⊆ V) (f : (α → ℝ) → β → ℝ)
    (hU : (univ : Set ℝ).Definable Language.ring U)
    (hf : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph V f)) :
    (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U f) := by
  convert (hU.preimage_comp Sum.inl).inter hf using 1
  ext v
  change (_ ∧ _) ↔ _ ∧ _ ∧ _
  exact ⟨fun h => ⟨h.1,hUV h.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩

theorem cad_selectedGraph_pair {α β γ : Type*}
    {U : Set (α → ℝ)} {f : (α → ℝ) → β → ℝ} {g : (α → ℝ) → γ → ℝ}
    (hf : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U f))
    (hg : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U g)) :
    (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph U (fun x => Sum.elim (f x) (g x))) := by
  let ef : α ⊕ β → α ⊕ (β ⊕ γ) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  let eg : α ⊕ γ → α ⊕ (β ⊕ γ) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)
  convert (hf.preimage_comp ef).inter (hg.preimage_comp eg) using 1
  ext v
  change (v ∘ Sum.inl ∈ U ∧ Sum.elim (f (v ∘ Sum.inl)) (g (v ∘ Sum.inl)) = v ∘ Sum.inr) ↔
    (v ∘ Sum.inl ∈ U ∧ f (v ∘ Sum.inl) = fun b => v (Sum.inr (Sum.inl b))) ∧
    (v ∘ Sum.inl ∈ U ∧ g (v ∘ Sum.inl) = fun c => v (Sum.inr (Sum.inr c)))
  constructor
  · rintro ⟨hu,h⟩
    exact ⟨⟨hu,funext (fun b => congrFun h (Sum.inl b))⟩,
      ⟨hu,funext (fun c => congrFun h (Sum.inr c))⟩⟩
  · rintro ⟨⟨hu,hf⟩,⟨_,hg⟩⟩
    refine ⟨hu,funext (fun i => ?_)⟩
    cases i with
    | inl b => exact congrFun hf b
    | inr c => exact congrFun hg c

theorem cad_selectedGraph_comp {α β γ : Type} [Finite α] [Finite β] [Finite γ]
    {U : Set (α → ℝ)} {V : Set (β → ℝ)}
    {f : (α → ℝ) → β → ℝ} {g : (β → ℝ) → γ → ℝ}
    (hf : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U f))
    (hg : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph V g))
    (hmap : MapsTo f U V) :
    (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U (g ∘ f)) := by
  let ef : α ⊕ β → (α ⊕ γ) ⊕ β := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  let eg : β ⊕ γ → (α ⊕ γ) ⊕ β := Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)
  have h := realDefinable_exists ((hf.preimage_comp ef).inter (hg.preimage_comp eg))
  convert h using 1
  ext v
  change (v ∘ Sum.inl ∈ U ∧ g (f (v ∘ Sum.inl)) = v ∘ Sum.inr) ↔
    ∃ w : β → ℝ, (v ∘ Sum.inl ∈ U ∧ f (v ∘ Sum.inl) = w) ∧
      (w ∈ V ∧ g w = v ∘ Sum.inr)
  constructor
  · rintro ⟨hu,hy⟩
    exact ⟨f (v ∘ Sum.inl),⟨hu,rfl⟩,hmap hu,hy⟩
  · rintro ⟨w,⟨hu,hw⟩,_,hy⟩
    exact ⟨hu,by simpa only [hw] using hy⟩

theorem cad_selectedGraph_polynomial {α β : Type} [Finite α] [Fintype β]
    {U : Set (α → ℝ)} (hU : (univ : Set ℝ).Definable Language.ring U)
    (q : β → MvPolynomial α ℝ) :
    (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph U (fun x b => MvPolynomial.eval x (q b))) := by
  have hEq := realDefinable_finite_all (fun b : β => realPolynomial_zero_definable
    (MvPolynomial.rename Sum.inl (q b) - MvPolynomial.X (Sum.inr b : α ⊕ β)))
  convert (hU.preimage_comp Sum.inl).inter hEq using 1
  ext v
  simp only [selectedFunctionGraph, mem_setOf_eq, mem_inter_iff, mem_preimage,
    map_sub, MvPolynomial.eval_X, MvPolynomial.eval_rename, sub_eq_zero,
    funext_iff, Function.comp_def]

theorem cad_selectedGraph_const {α β : Type} [Finite α] [Fintype β]
    {U : Set (α → ℝ)} (hU : (univ : Set ℝ).Definable Language.ring U) (c : β → ℝ) :
    (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U (fun _ => c)) := by
  simpa only [MvPolynomial.eval_C] using
    cad_selectedGraph_polynomial hU (fun b => MvPolynomial.C (c b))

theorem cad_selectedGraph_affineCombination {α : Type} [Finite α]
    {U : Set (α → ℝ)} {f g : (α → ℝ) → ℝ}
    (hf : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U (fun x (_ : Unit) => f x)))
    (hg : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U (fun x (_ : Unit) => g x)))
    (a b c : ℝ) :
    (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph U (fun x (_ : Unit) => a * f x + b * g x + c)) := by
  let q : Unit → MvPolynomial (Unit ⊕ Unit) ℝ := fun _ =>
    MvPolynomial.C a * MvPolynomial.X (Sum.inl ()) +
      MvPolynomial.C b * MvPolynomial.X (Sum.inr ()) + MvPolynomial.C c
  have hq := cad_selectedGraph_polynomial
    (Set.definable_univ : (univ : Set ℝ).Definable Language.ring (univ : Set ((Unit ⊕ Unit) → ℝ))) q
  have h := cad_selectedGraph_comp (cad_selectedGraph_pair hf hg) hq (fun _ _ => mem_univ _)
  simpa only [q, Function.comp_def, map_add, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr] using h

end PaperI
