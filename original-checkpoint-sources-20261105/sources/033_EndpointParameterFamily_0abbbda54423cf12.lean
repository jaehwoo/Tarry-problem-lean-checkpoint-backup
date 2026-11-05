import PaperILean.MarkedHardtPathTransport
import PaperILean.PublishedRealAlgebraicAssumptions

/-! Both endpoints are free parameters of the same original fiber. The new
family is empty unless both endpoints belong to that fiber. Its nonempty
fibers are exactly the original fibers. Sign-description consequences retain
the existing accepted qualitative QE input explicitly. -/

noncomputable section
namespace PaperI
open FirstOrder Set
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

abbrev EndpointParameter (α κ : Type*) := (α ⊕ κ) ⊕ κ

def endpointParameter {α κ : Type*} (p : α → ℝ) (x y : κ → ℝ) :
    EndpointParameter α κ → ℝ := Sum.elim (Sum.elim p x) y

def endpointParameterizedFamily {α κ : Type*} (A : Set ((α ⊕ κ) → ℝ)) :
    Set ((EndpointParameter α κ ⊕ κ) → ℝ) :=
  {v |
    Sum.elim (fun a => v (Sum.inl (Sum.inl (Sum.inl a))))
      (fun k => v (Sum.inl (Sum.inl (Sum.inr k)))) ∈ A ∧
    Sum.elim (fun a => v (Sum.inl (Sum.inl (Sum.inl a))))
      (fun k => v (Sum.inl (Sum.inr k))) ∈ A ∧
    Sum.elim (fun a => v (Sum.inl (Sum.inl (Sum.inl a))))
      (fun k => v (Sum.inr k)) ∈ A}

def endpointValue {α κ : Type*} (j : Fin 2)
    (b : EndpointParameter α κ → ℝ) : κ → ℝ :=
  if j = 0 then fun k => b (Sum.inl (Sum.inr k)) else fun k => b (Sum.inr k)

theorem endpointParameter_eta {α κ : Type*} (b : EndpointParameter α κ → ℝ) :
    endpointParameter (fun a => b (Sum.inl (Sum.inl a)))
      (fun k => b (Sum.inl (Sum.inr k))) (fun k => b (Sum.inr k)) = b := by
  funext i
  rcases i with (a | k) | k <;> rfl

theorem endpointValue_zero {α κ : Type*} (p : α → ℝ) (x y : κ → ℝ) :
    endpointValue 0 (endpointParameter p x y) = x := by
  simp only [endpointValue, ↓reduceIte, endpointParameter, Sum.elim_inl, Sum.elim_inr]

theorem endpointValue_one {α κ : Type*} (p : α → ℝ) (x y : κ → ℝ) :
    endpointValue 1 (endpointParameter p x y) = y := by
  simp [endpointValue, endpointParameter]

theorem endpointParameterizedFamily_mem {α κ : Type*} (A : Set ((α ⊕ κ) → ℝ))
    (p : α → ℝ) (x y z : κ → ℝ) :
    Sum.elim (endpointParameter p x y) z ∈ endpointParameterizedFamily A ↔
      x ∈ projectionFiber A p ∧ y ∈ projectionFiber A p ∧ z ∈ projectionFiber A p :=
  Iff.rfl

theorem endpointParameterizedFamily_domain {α κ : Type*} (A : Set ((α ⊕ κ) → ℝ))
    (p : α → ℝ) (x y : κ → ℝ) :
    endpointParameter p x y ∈ projectionDomain (endpointParameterizedFamily A) ↔
      x ∈ projectionFiber A p ∧ y ∈ projectionFiber A p := by
  change (∃ z, Sum.elim (endpointParameter p x y) z ∈ endpointParameterizedFamily A) ↔ _
  simp only [endpointParameterizedFamily_mem]
  exact ⟨fun ⟨_, hx, hy, _⟩ => ⟨hx, hy⟩, fun ⟨hx, hy⟩ => ⟨x, hx, hy, hx⟩⟩

theorem endpointParameterizedFamily_fiber {α κ : Type*} (A : Set ((α ⊕ κ) → ℝ))
    (p : α → ℝ) (x y : κ → ℝ) (hx : x ∈ projectionFiber A p)
    (hy : y ∈ projectionFiber A p) :
    projectionFiber (endpointParameterizedFamily A) (endpointParameter p x y) =
      projectionFiber A p := by
  ext z
  change Sum.elim (endpointParameter p x y) z ∈ endpointParameterizedFamily A ↔ _
  simp only [endpointParameterizedFamily_mem, hx, hy, true_and]

theorem endpointValue_mem {α κ : Type*} (A : Set ((α ⊕ κ) → ℝ))
    (j : Fin 2) (b : EndpointParameter α κ → ℝ)
    (hb : b ∈ projectionDomain (endpointParameterizedFamily A)) :
    endpointValue j b ∈ projectionFiber (endpointParameterizedFamily A) b := by
  rw [← endpointParameter_eta b] at hb ⊢
  obtain ⟨hx, hy⟩ := (endpointParameterizedFamily_domain A _ _ _).mp hb
  rw [endpointParameterizedFamily_fiber A _ _ _ hx hy]
  fin_cases j
  · simpa only [endpointValue_zero] using hx
  · simpa only [endpointValue_one] using hy

theorem endpointParameterizedFamily_isPreconnected {α κ : Type*}
    (A : Set ((α ⊕ κ) → ℝ))
    (hconn : ∀ p : α → ℝ, IsPreconnected (projectionFiber A p))
    (b : EndpointParameter α κ → ℝ) :
    IsPreconnected (projectionFiber (endpointParameterizedFamily A) b) := by
  by_cases hb : b ∈ projectionDomain (endpointParameterizedFamily A)
  · rw [← endpointParameter_eta b] at hb ⊢
    obtain ⟨hx, hy⟩ := (endpointParameterizedFamily_domain A _ _ _).mp hb
    rw [endpointParameterizedFamily_fiber A _ _ _ hx hy]
    exact hconn _
  · have hempty : projectionFiber (endpointParameterizedFamily A) b = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro z hz
      exact hb ⟨z, hz⟩
    rw [hempty]
    exact isPreconnected_empty

theorem endpointParameterizedFamily_definable {α κ : Type*}
    {A : Set ((α ⊕ κ) → ℝ)}
    (hA : (univ : Set ℝ).Definable Language.ring A) :
    (univ : Set ℝ).Definable Language.ring (endpointParameterizedFamily A) := by
  let ex : α ⊕ κ → EndpointParameter α κ ⊕ κ :=
    Sum.elim (fun a => Sum.inl (Sum.inl (Sum.inl a)))
      (fun k => Sum.inl (Sum.inl (Sum.inr k)))
  let ey : α ⊕ κ → EndpointParameter α κ ⊕ κ :=
    Sum.elim (fun a => Sum.inl (Sum.inl (Sum.inl a)))
      (fun k => Sum.inl (Sum.inr k))
  let ez : α ⊕ κ → EndpointParameter α κ ⊕ κ :=
    Sum.elim (fun a => Sum.inl (Sum.inl (Sum.inl a))) Sum.inr
  convert (hA.preimage_comp ex).inter ((hA.preimage_comp ey).inter (hA.preimage_comp ez)) using 1
  ext v
  have hx : v ∘ ex = Sum.elim (fun a => v (Sum.inl (Sum.inl (Sum.inl a))))
      (fun k => v (Sum.inl (Sum.inl (Sum.inr k)))) := by
    funext i
    cases i <;> rfl
  have hy : v ∘ ey = Sum.elim (fun a => v (Sum.inl (Sum.inl (Sum.inl a))))
      (fun k => v (Sum.inl (Sum.inr k))) := by
    funext i
    cases i <;> rfl
  have hz : v ∘ ez = Sum.elim (fun a => v (Sum.inl (Sum.inl (Sum.inl a))))
      (fun k => v (Sum.inr k)) := by
    funext i
    cases i <;> rfl
  simp only [endpointParameterizedFamily, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_preimage, hx, hy, hz]

theorem endpointParameterizedFamily_endpointGraph_definable {α κ : Type*}
    [Finite α] [Finite κ] {A : Set ((α ⊕ κ) → ℝ)}
    (hA : (univ : Set ℝ).Definable Language.ring A) (j : Fin 2) :
    (univ : Set ℝ).Definable Language.ring
      (endpointGraph (endpointParameterizedFamily A) (endpointValue j)) := by
  classical
  letI := Fintype.ofFinite κ
  have hd : (univ : Set ℝ).Definable Language.ring
      (projectionDomain (endpointParameterizedFamily A)) :=
    realDefinable_exists (endpointParameterizedFamily_definable hA)
  let e : κ → EndpointParameter α κ ⊕ κ := fun k =>
    if j = 0 then Sum.inl (Sum.inl (Sum.inr k)) else Sum.inl (Sum.inr k)
  have he : (univ : Set ℝ).Definable Language.ring
      {v : (EndpointParameter α κ ⊕ κ) → ℝ | ∀ k, v (Sum.inr k) = v (e k)} := by
    apply realDefinable_finite_all
    intro k
    convert realPolynomial_zero_definable
      (MvPolynomial.X (Sum.inr k) - MvPolynomial.X (e k)) using 1
    ext v
    simp only [Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X, sub_eq_zero]
  convert (hd.preimage_comp Sum.inl).inter he using 1
  ext v
  simp only [endpointGraph, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  apply and_congr Iff.rfl
  rw [funext_iff]
  apply forall_congr'
  intro k
  by_cases hj : j = 0 <;> simp only [endpointValue, e, hj, ↓reduceIte, Function.comp_def]

theorem published_endpointParameterizedFamily_sign_description
    (hQE : PublishedRealSemialgebraicity) {α κ : Type} [Finite α] [Finite κ]
    {A : Set ((α ⊕ κ) → ℝ)} (hA : HasPolynomialSignDescription A) :
    HasPolynomialSignDescription (endpointParameterizedFamily A) :=
  hQE.finite_sign_description _
    (endpointParameterizedFamily_definable (hasPolynomialSignDescription_definable hA))

theorem published_endpointParameterizedFamily_endpointGraph_sign_description
    (hQE : PublishedRealSemialgebraicity) {α κ : Type} [Finite α] [Finite κ]
    {A : Set ((α ⊕ κ) → ℝ)} (hA : HasPolynomialSignDescription A) (j : Fin 2) :
    HasPolynomialSignDescription
      (endpointGraph (endpointParameterizedFamily A) (endpointValue j)) :=
  hQE.finite_sign_description _
    (endpointParameterizedFamily_endpointGraph_definable
      (hasPolynomialSignDescription_definable hA) j)

end PaperI
