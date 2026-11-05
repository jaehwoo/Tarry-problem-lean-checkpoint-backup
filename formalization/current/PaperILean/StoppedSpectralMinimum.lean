import PaperILean.StoppedFourthCompactMinimum

/-! I625-638, I683 and I693: name the actual infimum values of the unchanged
stopped windows. On P>=2 the inherited compactness proofs give attainment,
positivity and bounded-parameter lower bounds. No power bound is claimed. -/

noncomputable section
namespace PaperI

theorem csInf_image_eq_of_minimizer {X : Type*} {K : Set X} {f : X → ℝ}
    {x : X} (hx : x ∈ K) (hmin : ∀ y ∈ K, f x ≤ f y) :
    sInf (f '' K) = f x := by
  apply IsLeast.csInf_eq
  exact ⟨⟨x, hx, rfl⟩, fun _ ⟨y, hy, he⟩ => he ▸ hmin y hy⟩

def stoppedNormalMinimum (k : ℕ) (P : ℝ) : ℝ :=
  sInf ((fun S : AugmentedState k => normalOrbitSingularValues k S 2) ''
    {S | AugmentedTranslationStopped P S})

def stoppedFourthMinimum (k : ℕ) (P : ℝ) : ℝ :=
  sInf ((fun S : AugmentedState k => augmentedOrbitSingularValues k S 3) ''
    {S | AugmentedTranslationStopped P S})

theorem stoppedNormalMinimum_spec (k : ℕ) (P : ℝ) (hP : 2 ≤ P) :
    ∃ S : AugmentedState k, AugmentedTranslationStopped P S ∧
      stoppedNormalMinimum k P = normalOrbitSingularValues k S 2 ∧
      0 < stoppedNormalMinimum k P ∧
      ∀ T : AugmentedState k, AugmentedTranslationStopped P T →
        stoppedNormalMinimum k P ≤ normalOrbitSingularValues k T 2 := by
  obtain ⟨S, hS, hpos, hmin⟩ := stopped_normalOrbit_minimum_attained k P hP
  have he : stoppedNormalMinimum k P = normalOrbitSingularValues k S 2 :=
    csInf_image_eq_of_minimizer hS hmin
  exact ⟨S, hS, he, he.symm ▸ hpos, he.symm ▸ hmin⟩

theorem stoppedFourthMinimum_spec (k : ℕ) (P : ℝ) (hP : 2 ≤ P) :
    ∃ S : AugmentedState k, AugmentedTranslationStopped P S ∧
      stoppedFourthMinimum k P = augmentedOrbitSingularValues k S 3 ∧
      0 < stoppedFourthMinimum k P ∧
      ∀ T : AugmentedState k, AugmentedTranslationStopped P T →
        stoppedFourthMinimum k P ≤ augmentedOrbitSingularValues k T 3 := by
  obtain ⟨S, hS, hpos, hmin⟩ := stopped_augmentedOrbit_fourth_minimum_attained k P hP
  have he : stoppedFourthMinimum k P = augmentedOrbitSingularValues k S 3 :=
    csInf_image_eq_of_minimizer hS hmin
  exact ⟨S, hS, he, he.symm ▸ hpos, he.symm ▸ hmin⟩

theorem stoppedNormalMinimum_pos (k : ℕ) (P : ℝ) (hP : 2 ≤ P) :
    0 < stoppedNormalMinimum k P := by
  obtain ⟨_, _, _, hpos, _⟩ := stoppedNormalMinimum_spec k P hP
  exact hpos

theorem stoppedFourthMinimum_pos (k : ℕ) (P : ℝ) (hP : 2 ≤ P) :
    0 < stoppedFourthMinimum k P := by
  obtain ⟨_, _, _, hpos, _⟩ := stoppedFourthMinimum_spec k P hP
  exact hpos

theorem stoppedNormalMinimum_eq_iff (k : ℕ) (P t : ℝ) (hP : 2 ≤ P) :
    t = stoppedNormalMinimum k P ↔
      ∃ S : AugmentedState k, AugmentedTranslationStopped P S ∧
        t = normalOrbitSingularValues k S 2 ∧
        ∀ T : AugmentedState k, AugmentedTranslationStopped P T →
          t ≤ normalOrbitSingularValues k T 2 := by
  obtain ⟨S, hS, he, _, hmin⟩ := stoppedNormalMinimum_spec k P hP
  constructor
  · rintro rfl
    exact ⟨S, hS, he, hmin⟩
  · rintro ⟨T, hT, ht, hleast⟩
    exact le_antisymm ((hleast S hS).trans_eq he.symm)
      ((hmin T hT).trans_eq ht.symm)

theorem stoppedFourthMinimum_eq_iff (k : ℕ) (P t : ℝ) (hP : 2 ≤ P) :
    t = stoppedFourthMinimum k P ↔
      ∃ S : AugmentedState k, AugmentedTranslationStopped P S ∧
        t = augmentedOrbitSingularValues k S 3 ∧
        ∀ T : AugmentedState k, AugmentedTranslationStopped P T →
          t ≤ augmentedOrbitSingularValues k T 3 := by
  obtain ⟨S, hS, he, _, hmin⟩ := stoppedFourthMinimum_spec k P hP
  constructor
  · rintro rfl
    exact ⟨S, hS, he, hmin⟩
  · rintro ⟨T, hT, ht, hleast⟩
    exact le_antisymm ((hleast S hS).trans_eq he.symm)
      ((hmin T hT).trans_eq ht.symm)

theorem stoppedNormalMinimum_bounded_parameter_lower_bound (k : ℕ) (P₀ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : ℝ, 2 ≤ P → P ≤ P₀ → c ≤ stoppedNormalMinimum k P := by
  obtain ⟨c, hc, hb⟩ := stopped_normalOrbit_bounded_parameter_lower_bound k P₀
  refine ⟨c, hc, fun P hP hP₀ => ?_⟩
  obtain ⟨S, hS, he, _, _⟩ := stoppedNormalMinimum_spec k P hP
  exact (hb P hP hP₀ S hS).trans_eq he.symm

theorem stoppedFourthMinimum_bounded_parameter_lower_bound (k : ℕ) (P₀ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : ℝ, 2 ≤ P → P ≤ P₀ → c ≤ stoppedFourthMinimum k P := by
  obtain ⟨c, hc, hb⟩ := stopped_augmentedOrbit_fourth_bounded_parameter_lower_bound k P₀
  refine ⟨c, hc, fun P hP hP₀ => ?_⟩
  obtain ⟨S, hS, he, _, _⟩ := stoppedFourthMinimum_spec k P hP
  exact (hb P hP hP₀ S hS).trans_eq he.symm

end PaperI
