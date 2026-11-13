import PaperILean.PlanarSquaredDistanceBand
import PaperILean.GraphDerivativeDefinability
import PaperILean.SemialgebraicRelationComposition

/-! I1259: one joint ring-definable family contains every coefficient and
the width as parameters. Quantifiers range over the full complement. Proper
Euclidean space supplied the minimum, so no arbitrary bounded search radius
or new parameter restriction is needed. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def planarSquaredDistPolynomial {α : Type*} (a b : Fin 2 → α) : MvPolynomial α ℝ :=
  (MvPolynomial.X (a 0)-MvPolynomial.X (b 0))^2+
    (MvPolynomial.X (a 1)-MvPolynomial.X (b 1))^2

theorem planarSquaredDistPolynomial_eval {α : Type*} (a b : Fin 2 → α) (v : α → ℝ) :
    MvPolynomial.eval v (planarSquaredDistPolynomial a b) =
      planarSquaredDist (v ∘ a) (v ∘ b) := by
  simp [planarSquaredDistPolynomial,planarSquaredDist,Function.comp_def]

def planarSquaredBandFamily {ρ : Type*} (G : Set ((ρ ⊕ Fin 2) → ℝ)) :
    Set (((ρ ⊕ Unit) ⊕ Fin 2) → ℝ) :=
  {v | (fun i => v (Sum.inr i)) ∈ planarSquaredBand
    (projectionFiber G (fun r => v (Sum.inl (Sum.inl r))))
    (v (Sum.inl (Sum.inr ())))}

theorem planarSquaredBandFamily_fiber {ρ : Type*} (G : Set ((ρ ⊕ Fin 2) → ℝ))
    (p : ρ → ℝ) (W : ℝ) :
    projectionFiber (planarSquaredBandFamily G) (Sum.elim p (fun _ => W)) =
      planarSquaredBand (projectionFiber G p) W := rfl

theorem planarSquaredBandFamily_definable {ρ : Type*} [Finite ρ]
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (planarSquaredBandFamily G) := by
  let β := (ρ ⊕ Unit) ⊕ Fin 2
  let e : ρ ⊕ Fin 2 → β ⊕ Fin 2 := Sum.elim
    (fun r => Sum.inl (Sum.inl (Sum.inl r))) Sum.inr
  let q := planarSquaredDistPolynomial
    (fun i : Fin 2 => Sum.inl (Sum.inr i) : Fin 2 → β ⊕ Fin 2) Sum.inr
  let w : MvPolynomial (β ⊕ Fin 2) ℝ :=
    MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr ())))
  have hLow := realDefinable_forall
    ((hG.preimage_comp e).union (realPolynomial_lt_definable (w^2) (4*q)))
  have hHigh := realDefinable_exists
    ((hG.preimage_comp e).compl.inter (realPolynomial_lt_definable q (16*w^2)))
  convert hLow.inter hHigh using 1
  ext v
  have he (y : Fin 2 → ℝ) : Sum.elim v y ∘ e =
      Sum.elim (fun r => v (Sum.inl (Sum.inl r))) y := by
    funext i
    cases i <;> rfl
  simp only [planarSquaredBandFamily,planarSquaredBand,projectionFiber,
    mem_setOf_eq,mem_inter_iff,mem_union,mem_compl_iff,mem_preimage,he,
    q,w,planarSquaredDistPolynomial_eval,map_pow,map_mul,map_ofNat,
    MvPolynomial.eval_X,Function.comp_def,Sum.elim_inl,Sum.elim_inr]
  apply and_congr
  · apply forall_congr'
    intro y
    change (_ ∉ G → _) ↔ (Sum.elim v y ∘ e ∈ G ∨ _)
    rw [he]
    tauto
  · apply exists_congr
    intro y
    change (_ ∉ G ∧ _) ↔ (Sum.elim v y ∘ e ∉ G ∧ _)
    rw [he]

/-- A fixed joint family has a single sign-format bound before W and all
coefficient valuations. Qualitative QE suffices because the full family,
not an individual fiber, is eliminated. -/
theorem published_planarSquaredBandFamily_uniform_format
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (G : Set ((ρ ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ s D : ℕ, ∀ (p : ρ → ℝ) (W : ℝ),
      ∃ A : Finset (MvPolynomial (Fin 2) ℝ), A.card ≤ s ∧
        (∀ q ∈ A, q.totalDegree ≤ D) ∧
        PolynomialSignDetermined A (planarSquaredBand (projectionFiber G p) W) := by
  obtain ⟨s,D,h⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format
    (hQE.finite_sign_description _ (planarSquaredBandFamily_definable hG))
  exact ⟨s,D,fun p W => h (Sum.elim p (fun _ => W))⟩

end PaperI
