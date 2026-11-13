import PaperILean.PolynomialRelationGlobalUpper

/-! The finite-sign description remains explicit. This is the subsequent
upper-growth implication, not a proof of real quantifier elimination. -/

noncomputable section
namespace PaperI

theorem sign_graph_rpow_upper
    (m : ℝ → ℝ)
    (hwindow : ∀ T : ℝ, ∃ b : ℝ, 0 < b ∧
      ∀ P : ℝ, 2 ≤ P → P ≤ T → |m P| ≤ b)
    (hdesc : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = m (v (Sum.inl ()))}) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → |m P| ≤ C * P ^ C := by
  have hu : ∀ (x : Unit → ℝ) (t u : ℝ),
      polynomialGraphCoordinates x t ∈
        {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧ v (Sum.inr ()) = m (v (Sum.inl ()))} →
      polynomialGraphCoordinates x u ∈
        {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧ v (Sum.inr ()) = m (v (Sum.inl ()))} →
      t = u := by
    intro x t u ht hu
    exact ht.2.trans hu.2.symm
  obtain ⟨q, hq, hrel⟩ := single_valued_sign_graph_polynomial_relation hdesc hu
  exact function_polynomial_relation_rpow_upper m hwindow q hq
    (fun P hP => hrel (fun _ => P) (m P) ⟨hP, rfl⟩)

end PaperI

