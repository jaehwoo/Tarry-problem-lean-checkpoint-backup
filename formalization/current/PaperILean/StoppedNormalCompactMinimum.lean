import PaperILean.AugmentedStoppedTopology
import PaperILean.LeastSingularValueContinuity
import PaperILean.NormalOrbitLeastSingularValue
import Mathlib.Topology.Order.Compact

/-! I625-638 and I683: continuity of the exact normal least singular value
and its positive lower bound on each bounded parameter window. Constants here
may depend on the upper endpoint; the uniform P-power estimate remains open. -/

noncomputable section
namespace PaperI

theorem continuous_normalOrbit_leastSingularValue (k : ℕ) :
    Continuous (fun S : AugmentedState k => normalOrbitSingularValues k S 2) := by
  exact (continuous_least_descendingSingularValue (m := AugmentedCoordinateIndex k)
    (n := 2)).comp (continuous_normalOrbitMatrix k)

theorem continuous_normalOrbit_leastSingularValue_parameter (k : ℕ) :
    Continuous (fun z : ℝ × AugmentedState k => normalOrbitSingularValues k z.2 2) :=
  (continuous_normalOrbit_leastSingularValue k).comp continuous_snd

/-- A compact positive continuous function has a positive lower bound; empty
sets are included, so no nonemptiness hypothesis is silently introduced. -/
theorem exists_pos_le_on_compact {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {f : X → ℝ}
    (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ f x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f x, hpos x hx, fun y hy => hmin hy⟩
  · exact ⟨1, by norm_num, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

/-- This constant may depend on k and P. No uniform power dependence is claimed. -/
theorem stopped_normalOrbit_fixed_parameter_lower_bound (k : ℕ) (P : ℝ)
    (hP : 2 ≤ P) :
    ∃ c : ℝ, 0 < c ∧ ∀ S : AugmentedState k, AugmentedTranslationStopped P S →
      c ≤ normalOrbitSingularValues k S 2 := by
  apply exists_pos_le_on_compact (isCompact_augmentedTranslationStopped k P)
    (continuous_normalOrbit_leastSingularValue k).continuousOn
  intro S hS
  exact stopped_normalOrbit_last_singularValue_pos_of_two_le hP S hS

/-- The constant is chosen before P and S, but may depend on the finite upper
endpoint P₀. This is the bounded-parameter compactness step, not a P-power bound. -/
theorem stopped_normalOrbit_bounded_parameter_lower_bound (k : ℕ) (P₀ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : ℝ, 2 ≤ P → P ≤ P₀ →
      ∀ S : AugmentedState k, AugmentedTranslationStopped P S →
        c ≤ normalOrbitSingularValues k S 2 := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_le_on_compact
    (isCompact_augmentedStoppedBoundedFamily k P₀)
    (continuous_normalOrbit_leastSingularValue_parameter k).continuousOn
    (fun z hz => stopped_normalOrbit_last_singularValue_pos_of_two_le hz.1 z.2 hz.2.2)
  exact ⟨c, hc, fun P hP hP₀ S hS => hbound (P, S) ⟨hP, hP₀, hS⟩⟩

theorem stopped_normalOrbit_bounded_parameter_coercivity (k : ℕ) (P₀ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : ℝ, 2 ≤ P → P ≤ P₀ →
      ∀ S : AugmentedState k, AugmentedTranslationStopped P S →
        ∀ v : Fin 3 → ℝ, c * coordinateL2Norm v ≤
          augmentedStateNorm (normalOrbitDifferential k S v) := by
  obtain ⟨c, hc, hbound⟩ := stopped_normalOrbit_bounded_parameter_lower_bound k P₀
  refine ⟨c, hc, fun P hP hP₀ S hS v => ?_⟩
  exact (mul_le_mul_of_nonneg_right (hbound P hP hP₀ S hS)
    (coordinateL2Norm_nonneg v)).trans (normalOrbit_last_singularValue_mul_norm_le S v)

end PaperI
