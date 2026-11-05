import PaperILean.OrderedSingularValueContinuity
import PaperILean.StoppedWindowNonempty

/-! I600, I625--638 and I693: continuity of all six full singular values and
the positive fourth minimum on fixed and bounded parameter windows. Constants
may depend on the bounded endpoint; no unbounded-P power estimate is claimed. -/
noncomputable section
namespace PaperI

theorem continuous_augmentedOrbitSingularValue (k : ℕ) (i : Fin 6) :
    Continuous (fun S : AugmentedState k => augmentedOrbitSingularValues k S i) :=
  (continuous_descendingSingularValue i).comp (continuous_augmentedOrbitMatrix k)

theorem continuous_augmentedOrbitSingularValues (k : ℕ) :
    Continuous (augmentedOrbitSingularValues k) :=
  continuous_pi fun i => continuous_augmentedOrbitSingularValue k i

theorem continuous_augmentedOrbit_fourthSingularValue (k : ℕ) :
    Continuous (fun S : AugmentedState k => augmentedOrbitSingularValues k S 3) :=
  continuous_augmentedOrbitSingularValue k 3

theorem continuous_augmentedOrbit_fourthSingularValue_parameter (k : ℕ) :
    Continuous (fun z : ℝ × AugmentedState k => augmentedOrbitSingularValues k z.2 3) :=
  (continuous_augmentedOrbit_fourthSingularValue k).comp continuous_snd

theorem stopped_augmentedOrbit_fourth_fixed_parameter_lower_bound (k : ℕ) (P : ℝ)
    (hP : 2 ≤ P) :
    ∃ c : ℝ, 0 < c ∧ ∀ S : AugmentedState k, AugmentedTranslationStopped P S →
      c ≤ augmentedOrbitSingularValues k S 3 := by
  apply exists_pos_le_on_compact (isCompact_augmentedTranslationStopped k P)
    (continuous_augmentedOrbit_fourthSingularValue k).continuousOn
  intro S hS
  exact stopped_augmentedOrbit_fourth_singularValue_pos_of_two_le hP S hS

/-- The same c works for every P in the bounded interval, and every stopped
state; its dependence on k and the finite upper endpoint is unrestricted. -/
theorem stopped_augmentedOrbit_fourth_bounded_parameter_lower_bound (k : ℕ) (P₀ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : ℝ, 2 ≤ P → P ≤ P₀ →
      ∀ S : AugmentedState k, AugmentedTranslationStopped P S →
        c ≤ augmentedOrbitSingularValues k S 3 := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_le_on_compact
    (isCompact_augmentedStoppedBoundedFamily k P₀)
    (continuous_augmentedOrbit_fourthSingularValue_parameter k).continuousOn
    (fun z hz => stopped_augmentedOrbit_fourth_singularValue_pos_of_two_le hz.1 z.2 hz.2.2)
  exact ⟨c, hc, fun P hP hP₀ S hS => hbound (P, S) ⟨hP, hP₀, hS⟩⟩

theorem stopped_augmentedOrbit_fourth_minimum_attained (k : ℕ) (P : ℝ) (hP : 2 ≤ P) :
    ∃ S : AugmentedState k, AugmentedTranslationStopped P S ∧
      0 < augmentedOrbitSingularValues k S 3 ∧
      ∀ T : AugmentedState k, AugmentedTranslationStopped P T →
        augmentedOrbitSingularValues k S 3 ≤ augmentedOrbitSingularValues k T 3 := by
  obtain ⟨S, hS, hmin⟩ := (isCompact_augmentedTranslationStopped k P).exists_isMinOn
    (augmentedTranslationStopped_nonempty k P hP)
    (continuous_augmentedOrbit_fourthSingularValue k).continuousOn
  exact ⟨S, hS, stopped_augmentedOrbit_fourth_singularValue_pos_of_two_le hP S hS,
    fun T hT => hmin hT⟩

end PaperI
