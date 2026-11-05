import PaperILean.ScalarRelationComposition
import PaperILean.SemialgebraicRelationComposition
import PaperILean.PublishedRealAlgebraicAssumptions
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple

/-! A count and degree bound for scalar relation composition, chosen before
both input polynomial families, coefficients, Boolean descriptions and sets.
The only published premise is qualitative real QE. Its joint finite sign
family is specialized after both coefficient blocks have been fixed; a finite
maximum removes the two Boolean-table choices. -/

noncomputable section
namespace PaperI
open FirstOrder
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
local instance scalarCompositionInputDecidableEq (κ : Type) : DecidableEq (Unit ⊕ κ) :=
  Classical.typeDecidableEq _
local instance scalarCompositionOutputDecidableEq (κ : Type) : DecidableEq (κ ⊕ Unit) :=
  Classical.typeDecidableEq _
local instance scalarCompositionPlaneDecidableEq : DecidableEq (Fin 2) :=
  Classical.typeDecidableEq _

def leftParameterExtension {ρ σ τ : Type*} (G : Set ((ρ ⊕ τ) → ℝ)) :
    Set (((ρ ⊕ σ) ⊕ τ) → ℝ) :=
  {v | v ∘ Sum.map Sum.inl id ∈ G}

def rightParameterExtension {ρ σ τ : Type*} (G : Set ((σ ⊕ τ) → ℝ)) :
    Set (((ρ ⊕ σ) ⊕ τ) → ℝ) :=
  {v | v ∘ Sum.map Sum.inr id ∈ G}

theorem leftParameterExtension_definable {ρ σ τ : Type*}
    {G : Set ((ρ ⊕ τ) → ℝ)}
    (hG : (Set.univ : Set ℝ).Definable Language.ring G) :
    (Set.univ : Set ℝ).Definable Language.ring (leftParameterExtension (σ := σ) G) :=
  hG.preimage_comp (Sum.map Sum.inl id)

theorem rightParameterExtension_definable {ρ σ τ : Type*}
    {G : Set ((σ ⊕ τ) → ℝ)}
    (hG : (Set.univ : Set ℝ).Definable Language.ring G) :
    (Set.univ : Set ℝ).Definable Language.ring (rightParameterExtension (ρ := ρ) G) :=
  hG.preimage_comp (Sum.map Sum.inr id)

theorem leftParameterExtension_fiber {ρ σ τ : Type*}
    (G : Set ((ρ ⊕ τ) → ℝ)) (p : ρ → ℝ) (q : σ → ℝ) :
    projectionFiber (leftParameterExtension G) (Sum.elim p q) = projectionFiber G p := by
  ext x
  have he : Sum.elim (Sum.elim p q) x ∘ Sum.map Sum.inl id = Sum.elim p x := by
    funext a
    cases a <;> rfl
  change (Sum.elim (Sum.elim p q) x ∘ Sum.map Sum.inl id ∈ G) ↔ Sum.elim p x ∈ G
  rw [he]

theorem rightParameterExtension_fiber {ρ σ τ : Type*}
    (G : Set ((σ ⊕ τ) → ℝ)) (p : ρ → ℝ) (q : σ → ℝ) :
    projectionFiber (rightParameterExtension G) (Sum.elim p q) = projectionFiber G q := by
  ext x
  have he : Sum.elim (Sum.elim p q) x ∘ Sum.map Sum.inr id = Sum.elim q x := by
    funext a
    cases a <;> rfl
  change (Sum.elim (Sum.elim p q) x ∘ Sum.map Sum.inr id ∈ G) ↔ Sum.elim q x ∈ G
  rw [he]

theorem published_bounded_tuple_scalar_composition_sign_format
    (hQE : PublishedRealSemialgebraicity) (κ : Type) [Fintype κ]
    (sΓ DΓ sF DF : ℕ) :
    ∃ sOut DOut : ℕ,
      ∀ (P : Fin sΓ → MvPolynomial (Unit ⊕ κ) ℝ)
        (Q : Fin sF → MvPolynomial (κ ⊕ Unit) ℝ),
      (∀ i, (P i).totalDegree ≤ DΓ) → (∀ i, (Q i).totalDegree ≤ DF) →
      ∀ (Γ : Set ((Unit ⊕ κ) → ℝ)) (F : Set ((κ ⊕ Unit) → ℝ)),
      PolynomialSignDetermined (Finset.univ.image P) Γ →
      PolynomialSignDetermined (Finset.univ.image Q) F →
      ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ DOut) ∧
        PolynomialSignDetermined B (scalarRelationComposition Γ F) := by
  classical
  let ρ := Fin sΓ × ((Unit ⊕ κ) → Fin (DΓ + 1))
  let σ := Fin sF × ((κ ⊕ Unit) → Fin (DF + 1))
  let C := (((Fin sΓ → Bool × Bool) → Bool) × ((Fin sF → Bool × Bool) → Bool))
  let G : C → Set (((ρ ⊕ σ) ⊕ Fin 2) → ℝ) := fun b =>
    scalarRelationCompositionFamily
      (leftParameterExtension (σ := σ) (universalPolynomialBooleanSet (Unit ⊕ κ) sΓ DΓ b.1))
      (rightParameterExtension (ρ := ρ) (universalPolynomialBooleanSet (κ ⊕ Unit) sF DF b.2))
  have hG : ∀ b : C, HasPolynomialSignDescription (G b) := by
    intro b
    apply hQE.finite_sign_description
    exact scalarRelationCompositionFamily_definable
      (leftParameterExtension_definable (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Unit ⊕ κ) sΓ DΓ b.1)))
      (rightParameterExtension_definable (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (κ ⊕ Unit) sF DF b.2)))
  have h := fun b : C => hasPolynomialSignDescription_uniform_fiber_sign_format (hG b)
  choose sc dc hbudget using h
  refine ⟨Finset.univ.sup sc, Finset.univ.sup dc, ?_⟩
  intro P Q hP hQ Γ F hΓ hF
  obtain ⟨bΓ, hΓEq⟩ := polynomialSignDetermined_exists_universal_fiber sΓ DΓ P hP Γ hΓ
  obtain ⟨bF, hFEq⟩ := polynomialSignDetermined_exists_universal_fiber sF DF Q hQ F hF
  let b : C := (bΓ, bF)
  obtain ⟨B, hcard, hdegree, hB⟩ := hbudget b
    (Sum.elim (polynomialFamilyCoefficients DΓ P) (polynomialFamilyCoefficients DF Q))
  have hfiber : projectionFiber (G b)
      (Sum.elim (polynomialFamilyCoefficients DΓ P) (polynomialFamilyCoefficients DF Q)) =
      scalarRelationComposition Γ F := by
    change projectionFiber (scalarRelationCompositionFamily _ _) _ = _
    rw [scalarRelationCompositionFamily_fiber, leftParameterExtension_fiber,
      rightParameterExtension_fiber]
    change scalarRelationComposition
      (projectionFiber (universalPolynomialBooleanSet (Unit ⊕ κ) sΓ DΓ bΓ)
        (polynomialFamilyCoefficients DΓ P))
      (projectionFiber (universalPolynomialBooleanSet (κ ⊕ Unit) sF DF bF)
        (polynomialFamilyCoefficients DF Q)) = _
    exact congrArg₂ scalarRelationComposition hΓEq.symm hFEq.symm
  refine ⟨B, hcard.trans (Finset.le_sup (f := sc) (Finset.mem_univ b)),
    fun q hq => (hdegree q hq).trans (Finset.le_sup (f := dc) (Finset.mem_univ b)), ?_⟩
  rwa [hfiber] at hB

/-- At-most input format allows zero/repeated atoms, coefficient cancellation,
empty input relations and degenerate intermediate coordinate spaces. -/
theorem published_bounded_scalar_composition_sign_format
    (hQE : PublishedRealSemialgebraicity) (κ : Type) [Fintype κ]
    (sΓ DΓ sF DF : ℕ) :
    ∃ sOut DOut : ℕ,
      ∀ (AΓ : Finset (MvPolynomial (Unit ⊕ κ) ℝ))
        (AF : Finset (MvPolynomial (κ ⊕ Unit) ℝ))
        (Γ : Set ((Unit ⊕ κ) → ℝ)) (F : Set ((κ ⊕ Unit) → ℝ)),
      AΓ.card ≤ sΓ → (∀ q ∈ AΓ, q.totalDegree ≤ DΓ) → PolynomialSignDetermined AΓ Γ →
      AF.card ≤ sF → (∀ q ∈ AF, q.totalDegree ≤ DF) → PolynomialSignDetermined AF F →
      ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ DOut) ∧
        PolynomialSignDetermined B (scalarRelationComposition Γ F) := by
  obtain ⟨sOut, DOut, h⟩ :=
    published_bounded_tuple_scalar_composition_sign_format hQE κ sΓ DΓ sF DF
  refine ⟨sOut, DOut, ?_⟩
  intro AΓ AF Γ F hΓcard hΓdegree hΓ hFcard hFdegree hF
  obtain ⟨P, hP, hΓP⟩ := exists_bounded_polynomial_tuple_of_signDetermined
    AΓ Γ sΓ DΓ hΓcard hΓdegree hΓ
  obtain ⟨Q, hQ, hFQ⟩ := exists_bounded_polynomial_tuple_of_signDetermined
    AF F sF DF hFcard hFdegree hF
  exact h P Q hP hQ Γ F hΓP hFQ

end PaperI
