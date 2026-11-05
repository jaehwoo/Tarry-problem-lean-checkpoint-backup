import PaperILean.QuantifiedPolynomialFormat

/-! A weak output-format consequence of BPR, second edition, Theorem 14.16.
For fixed free coordinates, ordered quantifier blocks, input polynomial count,
and total degree, bounds on the equivalent quantifier-free polynomial count
and degree precede every real coefficient and every Boolean matrix.

This contract does not postulate a component bound, a fiber cardinality bound,
or any manuscript-specific conclusion. The quantitative theorem itself is an
accepted external input, with no inhabitant supplied here. We retain existence
of format bounds, not the printed asymptotic complexity or coefficient-bit
estimates. The all-natural-number version includes elementary extensions:
empty blocks have the identity semantics proved in QuantifiedPolynomialFormat;
an empty prefix is already quantifier free; constant/empty matrices and zero
free coordinates are allowed. Positive printed complexity formulas are not
asserted at zero input budgets. Independent quantifier choices need not
alternate in BPR's definition of a `(P, Pi)` formula.

The checked bridge below turns the supplied quantifier-free Boolean formula
into the exact finite-sign interface used by the component-count application. -/

noncomputable section
namespace PaperI

/-- Accepted coefficient-uniform quantitative QE output, specialized to the
faithful prenex polynomial-sign encoding. Both output bounds precede `p` and `b`.
The matrix can be any Boolean table, including false and true. -/
structure PublishedQuantitativeRealQE : Prop where
  output_format : ∀ (α : Type) [Fintype α] (blocks : QuantifierPrefix) (s D : ℕ),
    ∃ sOut DOut : ℕ,
      ∀ (p : Fin s → MvPolynomial (α ⊕ Fin (quantifierVariableCount blocks)) ℝ),
        (∀ i, (p i).totalDegree ≤ D) →
        ∀ b : (Fin s → Bool × Bool) → Bool,
          ∃ t : ℕ, t ≤ sOut ∧
            ∃ (q : Fin t → MvPolynomial α ℝ) (c : (Fin t → Bool × Bool) → Bool),
              (∀ i, (q i).totalDegree ≤ DOut) ∧
              polynomialPrenexSet blocks p b = polynomialBooleanSet q c

/-- Quantifier-free output is converted, in Lean, to a bounded finite family of
polynomial signs. No output polynomial count is chosen after a coefficient. -/
theorem published_quantified_polynomial_sign_format
    (hQQE : PublishedQuantitativeRealQE)
    (α : Type) [Fintype α] (blocks : QuantifierPrefix) (s D : ℕ) :
    ∃ sOut DOut : ℕ,
      ∀ (p : Fin s → MvPolynomial (α ⊕ Fin (quantifierVariableCount blocks)) ℝ),
        (∀ i, (p i).totalDegree ≤ D) →
        ∀ b : (Fin s → Bool × Bool) → Bool,
          ∃ A : Finset (MvPolynomial α ℝ), A.card ≤ sOut ∧
            (∀ q ∈ A, q.totalDegree ≤ DOut) ∧
            PolynomialSignDetermined A (polynomialPrenexSet blocks p b) := by
  classical
  obtain ⟨sOut, DOut, hOut⟩ := hQQE.output_format α blocks s D
  refine ⟨sOut, DOut, ?_⟩
  intro p hp b
  obtain ⟨t, ht, q, c, hq, hEq⟩ := hOut p hp b
  refine ⟨Finset.univ.image q, ?_, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simpa using ht)
  · intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hq i
  · rw [hEq]
    exact polynomialBooleanSet_signDetermined q c

/-- A direct qualitative consequence keeps the quantitative published input
visible. It does not install an instance or prove that input inside Lean. -/
theorem published_polynomialPrenexSet_hasPolynomialSignDescription
    (hQQE : PublishedQuantitativeRealQE)
    {α : Type} [Fintype α] {s : ℕ} (blocks : QuantifierPrefix)
    (p : Fin s → MvPolynomial (α ⊕ Fin (quantifierVariableCount blocks)) ℝ)
    (b : (Fin s → Bool × Bool) → Bool) :
    HasPolynomialSignDescription (polynomialPrenexSet blocks p b) := by
  classical
  let D : ℕ := Finset.univ.sup (fun i => (p i).totalDegree)
  have hp : ∀ i, (p i).totalDegree ≤ D :=
    fun i => Finset.le_sup (f := fun j => (p j).totalDegree) (Finset.mem_univ i)
  obtain ⟨sOut, DOut, hOut⟩ := published_quantified_polynomial_sign_format hQQE α blocks s D
  obtain ⟨A, _, _, hA⟩ := hOut p hp b
  exact ⟨A, hA⟩

end PaperI
