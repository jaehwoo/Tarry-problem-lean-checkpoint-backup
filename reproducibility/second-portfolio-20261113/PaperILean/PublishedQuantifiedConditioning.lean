import PaperILean.BoundedQuantifiedFormat
import PaperILean.PublishedGeometricFiberBounds

/-! The original quantitative-QE, cell-decomposition and Hardt application in
I633/I638 for bounded prenex polynomial-sign families. Format bounds and the
common component/cardinality bound precede every coefficient, Boolean matrix
and external parameter. The source's positive-size quantifier blocks need no
extra block-count budget: their number is at most the number of quantified
scalar variables. A separate version also permits zero-size blocks with an
explicit length budget. No arbitrary-formula-to-prenex compiler is asserted.

Pre-strategy evidence: checkpoint_104_uniform_conditioning_pre_strategy.json
and the executed positive-block obstruction log. Empty geometric dimension
is -1; the dimension ≤0 cardinality conclusion includes that case exactly. -/

noncomputable section
namespace PaperI

/-- One N for all bounded prenex descriptions in fixed base and fiber spaces.
The output-format integers are obtained before the input coefficients. -/
theorem published_bounded_quantified_component_and_geometric_fiber_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hQQE : PublishedQuantitativeRealQE)
    (ι κ : Type) [Fintype ι] [Fintype κ] (B Q S D : ℕ) :
    ∃ N : ℕ, ∀ blocks : QuantifierPrefix, blocks.length ≤ B →
      quantifierVariableCount blocks ≤ Q → ∀ s : ℕ, s ≤ S →
      ∀ q : Fin s → MvPolynomial ((ι ⊕ κ) ⊕ Fin (quantifierVariableCount blocks)) ℝ,
      (∀ i, (q i).totalDegree ≤ D) →
      ∀ (b : (Fin s → Bool × Bool) → Bool) (p : ι → ℝ),
      (Finite (ConnectedComponents (projectionFiber (polynomialPrenexSet blocks q b) p)) ∧
        Nat.card (ConnectedComponents (projectionFiber (polynomialPrenexSet blocks q b) p)) ≤ N) ∧
      ∀ z : ℤ, HasGeometricSemialgebraicDimension
        (projectionFiber (polynomialPrenexSet blocks q b) p) z → z ≤ 0 →
        Finite (projectionFiber (polynomialPrenexSet blocks q b) p) ∧
          Nat.card (projectionFiber (polynomialPrenexSet blocks q b) p) ≤ N := by
  obtain ⟨sOut, DOut, hOut⟩ :=
    published_bounded_quantified_polynomial_sign_format hQQE (ι ⊕ κ) B Q S D
  obtain ⟨N, hN⟩ := published_bounded_sign_format_projection_fiber_component_bound
    hCells.toFiniteConnectedCover hHardt hQE κ sOut DOut
  refine ⟨N, ?_⟩
  intro blocks hB hQ s hs q hq b p
  obtain ⟨A, hAc, hAd, hAS⟩ := hOut blocks hB hQ s hs q hq b
  have hcomp := hN ι A (polynomialPrenexSet blocks q b) hAc hAd hAS p
  refine ⟨hcomp, ?_⟩
  intro z hz hle
  exact published_card_bound_of_geometric_dimension_le_zero hCells
    (projectionFiber (polynomialPrenexSet blocks q b) p)
    (projectionFiber_hasPolynomialSignDescription _ ⟨A, hAS⟩ p) hcomp hz hle

/-- All variable counts are now bounded before N, including base and fiber
coordinates; zero-size blocks are allowed under the explicit length bound B. -/
theorem published_at_most_quantified_component_and_geometric_fiber_bound
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hQQE : PublishedQuantitativeRealQE)
    (m₀ n₀ B Q S D : ℕ) :
    ∃ N : ℕ, ∀ m : ℕ, m ≤ m₀ → ∀ n : ℕ, n ≤ n₀ →
      ∀ blocks : QuantifierPrefix, blocks.length ≤ B →
      quantifierVariableCount blocks ≤ Q → ∀ s : ℕ, s ≤ S →
      ∀ q : Fin s → MvPolynomial ((Fin m ⊕ Fin n) ⊕ Fin (quantifierVariableCount blocks)) ℝ,
      (∀ i, (q i).totalDegree ≤ D) →
      ∀ (b : (Fin s → Bool × Bool) → Bool) (p : Fin m → ℝ),
      (Finite (ConnectedComponents (projectionFiber (polynomialPrenexSet blocks q b) p)) ∧
        Nat.card (ConnectedComponents (projectionFiber (polynomialPrenexSet blocks q b) p)) ≤ N) ∧
      ∀ z : ℤ, HasGeometricSemialgebraicDimension
        (projectionFiber (polynomialPrenexSet blocks q b) p) z → z ≤ 0 →
        Finite (projectionFiber (polynomialPrenexSet blocks q b) p) ∧
          Nat.card (projectionFiber (polynomialPrenexSet blocks q b) p) ≤ N := by
  classical
  choose N hN using fun j : Fin (m₀ + 1) × Fin (n₀ + 1) =>
    published_bounded_quantified_component_and_geometric_fiber_bound
      hCells hHardt hQE hQQE (Fin j.1.val) (Fin j.2.val) B Q S D
  refine ⟨Finset.univ.sup N, ?_⟩
  intro m hm n hn blocks hB hQ s hs q hq b p
  let j : Fin (m₀ + 1) × Fin (n₀ + 1) :=
    (⟨m, Nat.lt_succ_of_le hm⟩, ⟨n, Nat.lt_succ_of_le hn⟩)
  have h := hN j blocks hB hQ s hs q hq b p
  have hsup : N j ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ j)
  refine ⟨⟨h.1.1, h.1.2.trans hsup⟩, ?_⟩
  intro z hz hle
  have hc := h.2 z hz hle
  exact ⟨hc.1, hc.2.trans hsup⟩

/-- With positive-size blocks, the quantified-variable count already bounds
block count. Zero-size blocks would invalidate this inequality. -/
theorem quantifierPrefix_length_le_variableCount_of_positive
    (blocks : QuantifierPrefix) (hpos : ∀ block ∈ blocks, 0 < block.2) :
    blocks.length ≤ quantifierVariableCount blocks := by
  induction blocks with
  | nil => simp [quantifierVariableCount]
  | cons a tail ih =>
      have ha := hpos a (by simp)
      have ht := ih (fun block hb => hpos block (by simp [hb]))
      simp only [List.length_cons, quantifierVariableCount]
      omega

/-- Source-standard nonempty quantifier blocks: N depends only on variable,
polynomial-count and degree bounds. It precedes quantifier order, coefficients,
Boolean matrices, and every external parameter. This is conditioning (ii) for
the faithful bounded prenex encoding, including its original geometric premise. -/
theorem published_positive_block_quantified_conditioning
    (hCells : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hQQE : PublishedQuantitativeRealQE)
    (m₀ n₀ Q S D : ℕ) :
    ∃ N : ℕ, ∀ m : ℕ, m ≤ m₀ → ∀ n : ℕ, n ≤ n₀ →
      ∀ blocks : QuantifierPrefix, (∀ block ∈ blocks, 0 < block.2) →
      quantifierVariableCount blocks ≤ Q → ∀ s : ℕ, s ≤ S →
      ∀ q : Fin s → MvPolynomial ((Fin m ⊕ Fin n) ⊕ Fin (quantifierVariableCount blocks)) ℝ,
      (∀ i, (q i).totalDegree ≤ D) →
      ∀ (b : (Fin s → Bool × Bool) → Bool) (p : Fin m → ℝ),
      (Finite (ConnectedComponents (projectionFiber (polynomialPrenexSet blocks q b) p)) ∧
        Nat.card (ConnectedComponents (projectionFiber (polynomialPrenexSet blocks q b) p)) ≤ N) ∧
      ∀ z : ℤ, HasGeometricSemialgebraicDimension
        (projectionFiber (polynomialPrenexSet blocks q b) p) z → z ≤ 0 →
        Finite (projectionFiber (polynomialPrenexSet blocks q b) p) ∧
          Nat.card (projectionFiber (polynomialPrenexSet blocks q b) p) ≤ N := by
  obtain ⟨N, hN⟩ := published_at_most_quantified_component_and_geometric_fiber_bound
    hCells hHardt hQE hQQE m₀ n₀ Q Q S D
  refine ⟨N, ?_⟩
  intro m hm n hn blocks hpos hQ s hs q hq b p
  exact hN m hm n hn blocks
    ((quantifierPrefix_length_le_variableCount_of_positive blocks hpos).trans hQ)
    hQ s hs q hq b p

end PaperI
