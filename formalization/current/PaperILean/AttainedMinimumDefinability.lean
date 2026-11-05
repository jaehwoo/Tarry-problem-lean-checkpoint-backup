import PaperILean.RealPolynomialDefinability

/-! I625-638: the exact attained-minimum graph is first-order definable.
The existential graph point is essential; empty and nonattaining fibers are
not filled by arbitrary lower bounds. No compactness or growth is assumed. -/

noncomputable section
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- Minimum of all values in a relation fiber; no uniqueness of witnesses. -/
def attainedFiberMinimumGraph {α β : Type*}
    (G : Set (((α ⊕ β) ⊕ Unit) → ℝ)) : Set ((α ⊕ Unit) → ℝ) :=
  {v | (∃ x : β → ℝ, Sum.elim (Sum.elim (v ∘ Sum.inl) x)
      (fun _ => v (Sum.inr ())) ∈ G) ∧
    ∀ (y : β → ℝ) (s : ℝ), Sum.elim (Sum.elim (v ∘ Sum.inl) y)
      (fun _ => s) ∈ G → v (Sum.inr ()) ≤ s}

theorem attainedFiberMinimumGraph_definable {α β : Type*} [Finite α] [Finite β]
    {G : Set (((α ⊕ β) ⊕ Unit) → ℝ)}
    (hG : (Set.univ : Set ℝ).Definable Language.ring G) :
    (Set.univ : Set ℝ).Definable Language.ring (attainedFiberMinimumGraph G) := by
  let e : (α ⊕ β) ⊕ Unit → (α ⊕ Unit) ⊕ β :=
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  let c : (α ⊕ β) ⊕ Unit → (α ⊕ Unit) ⊕ (β ⊕ Unit) :=
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)
  have he := realDefinable_exists (hG.preimage_comp e)
  have hl := realPolynomial_le_definable
    (MvPolynomial.X (Sum.inl (Sum.inr ()) : (α ⊕ Unit) ⊕ (β ⊕ Unit)))
    (MvPolynomial.X (Sum.inr (Sum.inr ())))
  have hc := realDefinable_forall ((hG.preimage_comp c).compl.union hl)
  convert he.inter hc using 1
  ext v
  simp only [attainedFiberMinimumGraph, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_union, Set.mem_compl_iff, MvPolynomial.eval_X]
  have heq (x : β → ℝ) : Sum.elim v x ∘ e =
      Sum.elim (Sum.elim (v ∘ Sum.inl) x) (fun _ => v (Sum.inr ())) := by
    funext a; rcases a with (a | b) | ⟨⟩ <;> rfl
  simp_rw [heq]
  apply and_congr_right
  intro _
  constructor
  · intro h w
    have hw : Sum.elim v w ∘ c =
        Sum.elim (Sum.elim (v ∘ Sum.inl) (w ∘ Sum.inl))
          (fun _ => w (Sum.inr ())) := by
      funext a; rcases a with (a | b) | ⟨⟩ <;> rfl
    rw [hw]
    exact or_iff_not_imp_left.mpr (fun hg => h (w ∘ Sum.inl) (w (Sum.inr ())) (not_not.mp hg))
  · intro h y s hy
    have hc' : Sum.elim v (Sum.elim y (fun _ => s)) ∘ c =
        Sum.elim (Sum.elim (v ∘ Sum.inl) y) (fun _ => s) := by
      funext a; rcases a with (a | b) | ⟨⟩ <;> rfl
    have hw := h (Sum.elim y (fun _ => s))
    rw [hc'] at hw
    exact hw.resolve_left (not_not.mpr hy)

theorem attainedFiberMinimumGraph_function_iff {α β : Type*}
    (K : (α → ℝ) → (β → ℝ) → Prop)
    (f : (α → ℝ) → (β → ℝ) → ℝ) (p : α → ℝ) (t : ℝ) :
    Sum.elim p (fun _ => t) ∈ attainedFiberMinimumGraph
      {v | K (fun a => v (Sum.inl (Sum.inl a)))
        (fun b => v (Sum.inl (Sum.inr b))) ∧
        v (Sum.inr ()) = f (fun a => v (Sum.inl (Sum.inl a)))
          (fun b => v (Sum.inl (Sum.inr b)))} ↔
      ∃ x, K p x ∧ t = f p x ∧ ∀ y, K p y → t ≤ f p y := by
  simp only [attainedFiberMinimumGraph, Set.mem_setOf_eq, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨⟨x, hx, ht⟩, h⟩
    exact ⟨x, hx, ht, fun y hy => h y (f p y) ⟨hy, rfl⟩⟩
  · rintro ⟨x, hx, ht, h⟩
    exact ⟨⟨x, hx, ht⟩, fun y s hs => (h y hs.1).trans_eq hs.2.symm⟩

theorem attainedFiberMinimumGraph_value_unique {α β : Type*}
    {G : Set (((α ⊕ β) ⊕ Unit) → ℝ)} {p : α → ℝ} {t u : ℝ}
    (ht : Sum.elim p (fun _ => t) ∈ attainedFiberMinimumGraph G)
    (hu : Sum.elim p (fun _ => u) ∈ attainedFiberMinimumGraph G) : t = u := by
  obtain ⟨⟨x, hx⟩, ht⟩ := ht
  obtain ⟨⟨y, hy⟩, hu⟩ := hu
  exact le_antisymm (ht y u hy) (hu x t hx)

theorem attainedFiberMinimumGraph_empty {α β : Type*} :
    attainedFiberMinimumGraph (∅ : Set (((α ⊕ β) ⊕ Unit) → ℝ)) = ∅ := by
  ext v
  simp [attainedFiberMinimumGraph]

end PaperI
