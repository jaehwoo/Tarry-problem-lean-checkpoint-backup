import PaperILean.SignGraphPowerLower
import PaperILean.StoppedMinimumPolynomialRelations

/-! I683 and I693, conditional only on the finite-sign descriptions of the
exact two minimum graphs. These premises are NOT discharged here. -/

noncomputable section
namespace PaperI

theorem stoppedNormalMinimum_rpow_lower_of_sign_description (k : ℕ)
    (hdesc : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedNormalMinimum k (v (Sum.inl ()))}) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → P ^ (-C) ≤ stoppedNormalMinimum k P :=
  positive_sign_graph_rpow_lower (stoppedNormalMinimum k)
    (stoppedNormalMinimum_pos k) (stoppedNormalMinimum_bounded_parameter_lower_bound k) hdesc

theorem stoppedFourthMinimum_rpow_lower_of_sign_description (k : ℕ)
    (hdesc : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedFourthMinimum k (v (Sum.inl ()))}) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → P ^ (-C) ≤ stoppedFourthMinimum k P :=
  positive_sign_graph_rpow_lower (stoppedFourthMinimum k)
    (stoppedFourthMinimum_pos k) (stoppedFourthMinimum_bounded_parameter_lower_bound k) hdesc

theorem stopped_normal_rpow_lower_of_sign_description (k : ℕ)
    (hdesc : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedNormalMinimum k (v (Sum.inl ()))}) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → ∀ S : AugmentedState k,
      AugmentedTranslationStopped P S → P ^ (-C) ≤ normalOrbitSingularValues k S 2 := by
  rcases stoppedNormalMinimum_rpow_lower_of_sign_description k hdesc with ⟨C, hC, hb⟩
  refine ⟨C, hC, fun P hP S hS => ?_⟩
  obtain ⟨_, _, _, _, hmin⟩ := stoppedNormalMinimum_spec k P hP
  exact (hb P hP).trans (hmin S hS)

theorem stopped_fourth_rpow_lower_of_sign_description (k : ℕ)
    (hdesc : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedFourthMinimum k (v (Sum.inl ()))}) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → ∀ S : AugmentedState k,
      AugmentedTranslationStopped P S → P ^ (-C) ≤ augmentedOrbitSingularValues k S 3 := by
  rcases stoppedFourthMinimum_rpow_lower_of_sign_description k hdesc with ⟨C, hC, hb⟩
  refine ⟨C, hC, fun P hP S hS => ?_⟩
  obtain ⟨_, _, _, _, hmin⟩ := stoppedFourthMinimum_spec k P hP
  exact (hb P hP).trans (hmin S hS)

theorem stopped_normal_fourth_rpow_lower_of_sign_descriptions (k : ℕ)
    (hnormal : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedNormalMinimum k (v (Sum.inl ()))})
    (hfourth : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedFourthMinimum k (v (Sum.inl ()))}) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → ∀ S : AugmentedState k,
      AugmentedTranslationStopped P S →
        P ^ (-C) ≤ normalOrbitSingularValues k S 2 ∧
        P ^ (-C) ≤ augmentedOrbitSingularValues k S 3 := by
  rcases stopped_normal_rpow_lower_of_sign_description k hnormal with ⟨C, hC, hn⟩
  rcases stopped_fourth_rpow_lower_of_sign_description k hfourth with ⟨D, hD, hf⟩
  refine ⟨max C D, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro P hP S hS
  have hP1 : 1 ≤ P := le_trans (by norm_num) hP
  exact ⟨(Real.rpow_le_rpow_of_exponent_le hP1 (neg_le_neg (le_max_left _ _))).trans
      (hn P hP S hS),
    (Real.rpow_le_rpow_of_exponent_le hP1 (neg_le_neg (le_max_right _ _))).trans
      (hf P hP S hS)⟩

end PaperI
