import PaperILean.PolynomialRelationGlobalLower

/-! The elimination premise is explicit. This theorem proves the subsequent
lower-growth step for a positive function with bounded-window lower bounds. -/

noncomputable section
namespace PaperI

theorem positive_sign_graph_rpow_lower
    (m : ℝ → ℝ) (hpos : ∀ P : ℝ, 2 ≤ P → 0 < m P)
    (hwindow : ∀ T : ℝ, ∃ b : ℝ, 0 < b ∧
      ∀ P : ℝ, 2 ≤ P → P ≤ T → b ≤ m P)
    (hdesc : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = m (v (Sum.inl ()))}) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → P ^ (-C) ≤ m P := by
  have hu : ∀ (x : Unit → ℝ) (t u : ℝ),
      polynomialGraphCoordinates x t ∈
        {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧ v (Sum.inr ()) = m (v (Sum.inl ()))} →
      polynomialGraphCoordinates x u ∈
        {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧ v (Sum.inr ()) = m (v (Sum.inl ()))} →
      t = u := by
    intro x t u ht hu
    exact ht.2.trans hu.2.symm
  rcases single_valued_sign_graph_polynomial_relation hdesc hu with ⟨q, hq, hrel⟩
  exact positive_function_polynomial_relation_rpow_lower m hpos hwindow q hq
    (fun P hP => hrel (fun _ => P) (m P) ⟨hP, rfl⟩)

end PaperI
