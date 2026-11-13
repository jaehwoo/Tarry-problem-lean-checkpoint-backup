import PaperILean.PublishedQuantitativeQE
import Mathlib.Data.List.OfFn

/-! Finite aggregation of quantitative-QE output budgets. An explicit bound on
prefix length is retained, since arbitrary zero-size blocks would defeat a
length bound inferred from the total number of bound variables alone. All
block orders and Boolean matrices remain admissible. The final output budgets
are chosen before the prefix, atom count, real coefficients, and Boolean table.
-/

noncomputable section
namespace PaperI

/-- Finite codes containing every prefix of at most B blocks with at most Q
quantified scalar coordinates. Some codes have a larger total; maximizing over
this finite superset is harmless and does not change any input formula. -/
abbrev QuantifierPrefixCode (B Q : ℕ) :=
  (length : Fin (B + 1)) × (Fin length.val → Bool × Fin (Q + 1))

def quantifierPrefixDecode {B Q : ℕ} (code : QuantifierPrefixCode B Q) :
    QuantifierPrefix := List.ofFn (fun i => ((code.2 i).1, (code.2 i).2.val))

theorem quantifierBlock_size_le_total (blocks : QuantifierPrefix)
    (block : Bool × ℕ) (hblock : block ∈ blocks) :
    block.2 ≤ quantifierVariableCount blocks := by
  induction blocks with
  | nil => simp at hblock
  | cons a tail ih =>
    rcases List.mem_cons.mp hblock with h | h
    · subst block
      exact Nat.le_add_right _ _
    · have ht := ih h
      change block.2 ≤ a.2 + quantifierVariableCount tail
      omega

def quantifierPrefixEncode (B Q : ℕ) (blocks : QuantifierPrefix)
    (hlen : blocks.length ≤ B) (hcount : quantifierVariableCount blocks ≤ Q) :
    QuantifierPrefixCode B Q :=
  ⟨⟨blocks.length, Nat.lt_succ_of_le hlen⟩,
    fun i => ((blocks.get i).1, ⟨(blocks.get i).2,
      Nat.lt_succ_of_le ((quantifierBlock_size_le_total blocks _
        (List.get_mem blocks i)).trans hcount)⟩)⟩

theorem quantifierPrefix_decode_encode (B Q : ℕ) (blocks : QuantifierPrefix)
    (hlen : blocks.length ≤ B) (hcount : quantifierVariableCount blocks ≤ Q) :
    quantifierPrefixDecode (quantifierPrefixEncode B Q blocks hlen hcount) = blocks := by
  change List.ofFn (fun i => ((blocks.get i).1, (blocks.get i).2)) = blocks
  simpa only [Prod.mk.eta] using List.ofFn_get blocks

/-- Existence of output-format bounds for all bounded prenex profiles at once.
The total quantified-variable bound Q and the separate block-count bound B
are both explicit, including zero-size blocks and zero atoms. -/
theorem published_bounded_quantified_polynomial_sign_format
    (hQQE : PublishedQuantitativeRealQE) (α : Type) [Fintype α]
    (B Q S D : ℕ) :
    ∃ sOut DOut : ℕ,
      ∀ blocks : QuantifierPrefix, blocks.length ≤ B →
        quantifierVariableCount blocks ≤ Q →
        ∀ s : ℕ, s ≤ S →
          ∀ (p : Fin s → MvPolynomial (α ⊕ Fin (quantifierVariableCount blocks)) ℝ),
            (∀ i, (p i).totalDegree ≤ D) →
            ∀ b : (Fin s → Bool × Bool) → Bool,
              ∃ A : Finset (MvPolynomial α ℝ), A.card ≤ sOut ∧
                (∀ q ∈ A, q.totalDegree ≤ DOut) ∧
                PolynomialSignDetermined A (polynomialPrenexSet blocks p b) := by
  classical
  let Index := QuantifierPrefixCode B Q × Fin (S + 1)
  choose count degree hOut using fun j : Index =>
    published_quantified_polynomial_sign_format hQQE α (quantifierPrefixDecode j.1) j.2.val D
  refine ⟨Finset.univ.sup count, Finset.univ.sup degree, ?_⟩
  intro blocks hlen hcount s hs p hp b
  let code := quantifierPrefixEncode B Q blocks hlen hcount
  let j : Index := (code, ⟨s, Nat.lt_succ_of_le hs⟩)
  have hj := hOut j
  have hdecode : quantifierPrefixDecode j.1 = blocks :=
    quantifierPrefix_decode_encode B Q blocks hlen hcount
  rw [hdecode] at hj
  obtain ⟨A, hA, hdegree, hsign⟩ := hj p hp b
  refine ⟨A, hA.trans (Finset.le_sup (f := count) (Finset.mem_univ j)), ?_, hsign⟩
  intro q hq
  exact (hdegree q hq).trans (Finset.le_sup (f := degree) (Finset.mem_univ j))

/-- One pair of output budgets also precedes the free-coordinate count n≤n0.
All quantified variables are counted by Q, independently of the free variables. -/
theorem published_at_most_quantified_polynomial_sign_format
    (hQQE : PublishedQuantitativeRealQE) (n0 B Q S D : ℕ) :
    ∃ sOut DOut : ℕ,
      ∀ n : ℕ, n ≤ n0 → ∀ blocks : QuantifierPrefix, blocks.length ≤ B →
        quantifierVariableCount blocks ≤ Q →
        ∀ s : ℕ, s ≤ S →
          ∀ (p : Fin s → MvPolynomial (Fin n ⊕ Fin (quantifierVariableCount blocks)) ℝ),
            (∀ i, (p i).totalDegree ≤ D) →
            ∀ b : (Fin s → Bool × Bool) → Bool,
              ∃ A : Finset (MvPolynomial (Fin n) ℝ), A.card ≤ sOut ∧
                (∀ q ∈ A, q.totalDegree ≤ DOut) ∧
                PolynomialSignDetermined A (polynomialPrenexSet blocks p b) := by
  classical
  choose count degree hOut using fun n : Fin (n0 + 1) =>
    published_bounded_quantified_polynomial_sign_format hQQE (Fin n.val) B Q S D
  refine ⟨Finset.univ.sup count, Finset.univ.sup degree, ?_⟩
  intro n hn blocks hlen hcount s hs p hp b
  let j : Fin (n0 + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  obtain ⟨A, hA, hdegree, hsign⟩ := hOut j blocks hlen hcount s hs p hp b
  refine ⟨A, hA.trans (Finset.le_sup (f := count) (Finset.mem_univ j)), ?_, hsign⟩
  intro q hq
  exact (hdegree q hq).trans (Finset.le_sup (f := degree) (Finset.mem_univ j))

end PaperI
