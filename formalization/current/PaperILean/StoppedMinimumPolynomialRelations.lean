import PaperILean.SignGraphPolynomialRelation
import PaperILean.StoppedMinimumFirstOrderGraphs

/-! I625-638, I683 and I693: conditional polynomial relations for the exact
stopped minima, with one polynomial chosen before all P >= 2. The missing
real-quantifier-elimination bridge is an explicit finite-sign-description
hypothesis, not a project axiom. These are not power-growth estimates. -/

noncomputable section
namespace PaperI

theorem stoppedNormalMinimum_polynomial_relation_of_sign_description (k : ℕ)
    (hdesc : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedNormalMinimum k (v (Sum.inl ()))}) :
    ∃ q : MvPolynomial (Unit ⊕ Unit) ℝ, q ≠ 0 ∧
      ∀ P : ℝ, 2 ≤ P →
        MvPolynomial.eval (minimumParameterCoordinates P (stoppedNormalMinimum k P)) q = 0 := by
  have hu : ∀ (x : Unit → ℝ) (t u : ℝ),
      polynomialGraphCoordinates x t ∈
        {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
          v (Sum.inr ()) = stoppedNormalMinimum k (v (Sum.inl ()))} →
      polynomialGraphCoordinates x u ∈
        {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
          v (Sum.inr ()) = stoppedNormalMinimum k (v (Sum.inl ()))} → t = u := by
    intro x t u ht hu
    exact ht.2.trans hu.2.symm
  obtain ⟨q, hq, he⟩ := single_valued_sign_graph_polynomial_relation hdesc hu
  refine ⟨q, hq, ?_⟩
  intro P hP
  exact he (fun _ => P) (stoppedNormalMinimum k P) ⟨hP, rfl⟩

theorem stoppedFourthMinimum_polynomial_relation_of_sign_description (k : ℕ)
    (hdesc : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedFourthMinimum k (v (Sum.inl ()))}) :
    ∃ q : MvPolynomial (Unit ⊕ Unit) ℝ, q ≠ 0 ∧
      ∀ P : ℝ, 2 ≤ P →
        MvPolynomial.eval (minimumParameterCoordinates P (stoppedFourthMinimum k P)) q = 0 := by
  have hu : ∀ (x : Unit → ℝ) (t u : ℝ),
      polynomialGraphCoordinates x t ∈
        {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
          v (Sum.inr ()) = stoppedFourthMinimum k (v (Sum.inl ()))} →
      polynomialGraphCoordinates x u ∈
        {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
          v (Sum.inr ()) = stoppedFourthMinimum k (v (Sum.inl ()))} → t = u := by
    intro x t u ht hu
    exact ht.2.trans hu.2.symm
  obtain ⟨q, hq, he⟩ := single_valued_sign_graph_polynomial_relation hdesc hu
  refine ⟨q, hq, ?_⟩
  intro P hP
  exact he (fun _ => P) (stoppedFourthMinimum k P) ⟨hP, rfl⟩

end PaperI
