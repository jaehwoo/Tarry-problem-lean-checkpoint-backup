import PaperILean.PolynomialFiberFormat
import PaperILean.RealPolynomialDefinability

/-! Composition of actual graph relations with one shared intermediate vector.
Partial domains are preserved. A finite polynomial-sign description of the
joint graph yields one count and degree bound before every base parameter.
No published result is assumed in this module. Pre-strategy obstructions:
`evidence/checkpoint_107_path_pre_strategy.json`. -/

noncomputable section
namespace PaperI
open FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def relationGraphComposition {ρ τ ξ ν : Type*}
    (Γ : Set (((ρ ⊕ τ) ⊕ ξ) → ℝ))
    (F : Set (((ρ ⊕ ξ) ⊕ ν) → ℝ)) : Set (((ρ ⊕ τ) ⊕ ν) → ℝ) :=
  {v | ∃ x : ξ → ℝ,
    Sum.elim (fun a => v (Sum.inl a)) x ∈ Γ ∧
    Sum.elim (Sum.elim (fun a => v (Sum.inl (Sum.inl a))) x)
      (fun a => v (Sum.inr a)) ∈ F}

theorem relationGraphComposition_mem {ρ τ ξ ν : Type*}
    (Γ : Set (((ρ ⊕ τ) ⊕ ξ) → ℝ))
    (F : Set (((ρ ⊕ ξ) ⊕ ν) → ℝ))
    (p : ρ → ℝ) (t : τ → ℝ) (z : ν → ℝ) :
    Sum.elim (Sum.elim p t) z ∈ relationGraphComposition Γ F ↔
      ∃ x : ξ → ℝ, Sum.elim (Sum.elim p t) x ∈ Γ ∧
        Sum.elim (Sum.elim p x) z ∈ F := Iff.rfl

theorem relationGraphComposition_definable {ρ τ ξ ν : Type*}
    [Finite ρ] [Finite τ] [Finite ξ] [Finite ν]
    {Γ : Set (((ρ ⊕ τ) ⊕ ξ) → ℝ)}
    {F : Set (((ρ ⊕ ξ) ⊕ ν) → ℝ)}
    (hΓ : (Set.univ : Set ℝ).Definable Language.ring Γ)
    (hF : (Set.univ : Set ℝ).Definable Language.ring F) :
    (Set.univ : Set ℝ).Definable Language.ring (relationGraphComposition Γ F) := by
  let eΓ : (ρ ⊕ τ) ⊕ ξ → ((ρ ⊕ τ) ⊕ ν) ⊕ ξ :=
    Sum.elim (fun a => Sum.inl (Sum.inl a)) Sum.inr
  let eF : (ρ ⊕ ξ) ⊕ ν → ((ρ ⊕ τ) ⊕ ν) ⊕ ξ :=
    Sum.elim (Sum.elim (fun a => Sum.inl (Sum.inl (Sum.inl a))) Sum.inr)
      (fun a => Sum.inl (Sum.inr a))
  have h := realDefinable_exists ((hΓ.preimage_comp eΓ).inter (hF.preimage_comp eF))
  convert h using 1
  ext v
  apply exists_congr
  intro x
  have heΓ : Sum.elim v x ∘ eΓ = Sum.elim (fun a => v (Sum.inl a)) x := by
    funext a
    cases a <;> rfl
  have heF : Sum.elim v x ∘ eF =
      Sum.elim (Sum.elim (fun a => v (Sum.inl (Sum.inl a))) x)
        (fun a => v (Sum.inr a)) := by
    funext a
    rcases a with (a | a) | a <;> rfl
  simp only [Set.mem_inter_iff, Set.mem_preimage, heΓ, heF]

def relationGraphCompositionParametric {ρ τ ξ ν : Type*}
    (Γ : Set (((ρ ⊕ τ) ⊕ ξ) → ℝ))
    (F : Set (((ρ ⊕ ξ) ⊕ ν) → ℝ)) : Set ((ρ ⊕ (τ ⊕ ν)) → ℝ) :=
  {v | v ∘ Equiv.sumAssoc ρ τ ν ∈ relationGraphComposition Γ F}

theorem relationGraphCompositionParametric_mem {ρ τ ξ ν : Type*}
    (Γ : Set (((ρ ⊕ τ) ⊕ ξ) → ℝ))
    (F : Set (((ρ ⊕ ξ) ⊕ ν) → ℝ))
    (p : ρ → ℝ) (t : τ → ℝ) (z : ν → ℝ) :
    Sum.elim p (Sum.elim t z) ∈ relationGraphCompositionParametric Γ F ↔
      ∃ x : ξ → ℝ, Sum.elim (Sum.elim p t) x ∈ Γ ∧
        Sum.elim (Sum.elim p x) z ∈ F := by
  change Sum.elim p (Sum.elim t z) ∘ Equiv.sumAssoc ρ τ ν ∈
    relationGraphComposition Γ F ↔ _
  have hv : Sum.elim p (Sum.elim t z) ∘ Equiv.sumAssoc ρ τ ν =
      Sum.elim (Sum.elim p t) z := by
    funext a
    rcases a with (a | a) | a <;> rfl
  rw [hv, relationGraphComposition_mem]

theorem relationGraphCompositionParametric_definable {ρ τ ξ ν : Type*}
    [Finite ρ] [Finite τ] [Finite ξ] [Finite ν]
    {Γ : Set (((ρ ⊕ τ) ⊕ ξ) → ℝ)}
    {F : Set (((ρ ⊕ ξ) ⊕ ν) → ℝ)}
    (hΓ : (Set.univ : Set ℝ).Definable Language.ring Γ)
    (hF : (Set.univ : Set ℝ).Definable Language.ring F) :
    (Set.univ : Set ℝ).Definable Language.ring
      (relationGraphCompositionParametric Γ F) :=
  (relationGraphComposition_definable hΓ hF).preimage_comp (Equiv.sumAssoc ρ τ ν)

theorem relationGraphCompositionParametric_eq_partialGraph {ρ τ ξ ν : Type*}
    (Γ : Set (((ρ ⊕ τ) ⊕ ξ) → ℝ))
    (F : Set (((ρ ⊕ ξ) ⊕ ν) → ℝ))
    (T : (ρ → ℝ) → Set (τ → ℝ)) (U : (ρ → ℝ) → Set (ξ → ℝ))
    (γ : (ρ → ℝ) → (τ → ℝ) → (ξ → ℝ))
    (f : (ρ → ℝ) → (ξ → ℝ) → (ν → ℝ))
    (hΓ : ∀ p t x, Sum.elim (Sum.elim p t) x ∈ Γ ↔ t ∈ T p ∧ x = γ p t)
    (hF : ∀ p x z, Sum.elim (Sum.elim p x) z ∈ F ↔ x ∈ U p ∧ z = f p x)
    (p : ρ → ℝ) :
    projectionFiber (relationGraphCompositionParametric Γ F) p = {v |
      (fun i => v (Sum.inl i)) ∈ T p ∧ γ p (fun i => v (Sum.inl i)) ∈ U p ∧
        (fun i => v (Sum.inr i)) = f p (γ p (fun i => v (Sum.inl i)))} := by
  ext v
  have hv : Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) = v := by
    funext a
    cases a <;> rfl
  have hm := relationGraphCompositionParametric_mem Γ F p
    (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i))
  rw [hv] at hm
  change Sum.elim p v ∈ relationGraphCompositionParametric Γ F ↔ _
  rw [hm]
  simp only [hΓ, hF, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨ht, rfl⟩, hu, hz⟩
    exact ⟨ht, hu, hz⟩
  · rintro ⟨ht, hu, hz⟩
    exact ⟨_, ⟨ht, rfl⟩, hu, hz⟩

theorem relationGraphCompositionParametric_eq_graph_on_domain {ρ τ ξ ν : Type*}
    (Γ : Set (((ρ ⊕ τ) ⊕ ξ) → ℝ))
    (F : Set (((ρ ⊕ ξ) ⊕ ν) → ℝ))
    (T : (ρ → ℝ) → Set (τ → ℝ)) (U : (ρ → ℝ) → Set (ξ → ℝ))
    (γ : (ρ → ℝ) → (τ → ℝ) → (ξ → ℝ))
    (f : (ρ → ℝ) → (ξ → ℝ) → (ν → ℝ))
    (hΓ : ∀ p t x, Sum.elim (Sum.elim p t) x ∈ Γ ↔ t ∈ T p ∧ x = γ p t)
    (hF : ∀ p x z, Sum.elim (Sum.elim p x) z ∈ F ↔ x ∈ U p ∧ z = f p x)
    (hmap : ∀ p t, t ∈ T p → γ p t ∈ U p) (p : ρ → ℝ) :
    projectionFiber (relationGraphCompositionParametric Γ F) p = {v |
      (fun i => v (Sum.inl i)) ∈ T p ∧
        (fun i => v (Sum.inr i)) = f p (γ p (fun i => v (Sum.inl i)))} := by
  rw [relationGraphCompositionParametric_eq_partialGraph Γ F T U γ f hΓ hF p]
  ext v
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hmap _ _ h.1, h.2⟩⟩

/-- The count and total degree are chosen from the joint finite family before
the parameter valuation, including empty and degenerate fibers. -/
theorem hasPolynomialSignDescription_uniform_fiber_sign_format {ρ κ : Type*}
    {G : Set ((ρ ⊕ κ) → ℝ)} (hG : HasPolynomialSignDescription G) :
    ∃ s D : ℕ, ∀ p : ρ → ℝ,
      ∃ A : Finset (MvPolynomial κ ℝ), A.card ≤ s ∧
        (∀ q ∈ A, q.totalDegree ≤ D) ∧
        PolynomialSignDetermined A (projectionFiber G p) := by
  classical
  obtain ⟨A, hA⟩ := hG
  refine ⟨A.card, A.sup MvPolynomial.totalDegree, ?_⟩
  intro p
  exact projectionFiber_has_bounded_sign_format p A G A.card
    (A.sup MvPolynomial.totalDegree) le_rfl (fun q hq => Finset.le_sup hq) hA

end PaperI
