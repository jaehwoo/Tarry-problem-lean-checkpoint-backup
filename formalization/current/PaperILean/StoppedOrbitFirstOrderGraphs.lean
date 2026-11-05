import PaperILean.StoppedStatePolynomialFamily
import PaperILean.PolynomialSingularValueDefinability

/-! I600, I623-638 and I668-694: fixed first-order formulas for the exact joint
stopped normal-least and full-fourth graphs. Constants and formulas are chosen
before P, state and value. This is not a proof of the uniform lower bounds. -/

noncomputable section
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

abbrev StoppedSpectralVariable (k : ℕ) := StoppedStateVariable k ⊕ Unit

def stoppedSpectralCoordinates {k : ℕ} (P : ℝ) (S : AugmentedState k) (t : ℝ) :
    StoppedSpectralVariable k → ℝ :=
  Sum.elim (stoppedStateCoordinates P S) (fun _ => t)

theorem eval_augmentedOrbitEntryPolynomial_coordinates (k : ℕ)
    (v : AugmentedCoordinateIndex k → ℝ) (r : AugmentedCoordinateIndex k) (j : Fin 6) :
    MvPolynomial.eval v (augmentedOrbitEntryPolynomial k r j) =
      augmentedOrbitMatrix k ((augmentedStateCoordinates k).symm v) r j := by
  simpa only [LinearEquiv.apply_symm_apply] using
    eval_augmentedOrbitEntryPolynomial k ((augmentedStateCoordinates k).symm v) r j

theorem eval_normalOrbitEntryPolynomial_coordinates (k : ℕ)
    (v : AugmentedCoordinateIndex k → ℝ) (r : AugmentedCoordinateIndex k) (j : Fin 3) :
    MvPolynomial.eval v (normalOrbitEntryPolynomial k r j) =
      normalOrbitMatrix k ((augmentedStateCoordinates k).symm v) r j := by
  simpa only [LinearEquiv.apply_symm_apply] using
    eval_normalOrbitEntryPolynomial k ((augmentedStateCoordinates k).symm v) r j

def stoppedNormalLeastFamily (k : ℕ) : Set (StoppedSpectralVariable k → ℝ) :=
  {v | 2 ≤ v (Sum.inl (Sum.inl ())) ∧
    AugmentedTranslationStopped (v (Sum.inl (Sum.inl ())))
      ((augmentedStateCoordinates k).symm (fun r => v (Sum.inl (Sum.inr r)))) ∧
    v (Sum.inr ()) = normalOrbitSingularValues k
      ((augmentedStateCoordinates k).symm (fun r => v (Sum.inl (Sum.inr r)))) 2}

def stoppedAugmentedFourthFamily (k : ℕ) : Set (StoppedSpectralVariable k → ℝ) :=
  {v | 2 ≤ v (Sum.inl (Sum.inl ())) ∧
    AugmentedTranslationStopped (v (Sum.inl (Sum.inl ())))
      ((augmentedStateCoordinates k).symm (fun r => v (Sum.inl (Sum.inr r)))) ∧
    v (Sum.inr ()) = augmentedOrbitSingularValues k
      ((augmentedStateCoordinates k).symm (fun r => v (Sum.inl (Sum.inr r)))) 3}

theorem stoppedNormalLeastFamily_definable (k : ℕ) :
    (Set.univ : Set ℝ).Definable Language.ring (stoppedNormalLeastFamily k) := by
  let A := fun r j => MvPolynomial.rename
    (fun i => (Sum.inl (Sum.inr i) : StoppedSpectralVariable k)) (normalOrbitEntryPolynomial k r j)
  have hg := polynomialSingularValueGraph_definable A (MvPolynomial.X (Sum.inr ())) 2
  have hs := (stoppedStateFamily_definable k).preimage_comp
    (Sum.inl : StoppedStateVariable k → StoppedSpectralVariable k)
  convert hs.inter hg using 1
  ext v
  simp only [stoppedNormalLeastFamily, stoppedStateFamily, Set.mem_setOf_eq,
    Set.mem_inter_iff, Set.mem_preimage, Function.comp_def, A,
    MvPolynomial.eval_X, MvPolynomial.eval_rename,
    eval_normalOrbitEntryPolynomial_coordinates, normalOrbitSingularValues, and_assoc]

theorem stoppedAugmentedFourthFamily_definable (k : ℕ) :
    (Set.univ : Set ℝ).Definable Language.ring (stoppedAugmentedFourthFamily k) := by
  let A := fun r j => MvPolynomial.rename
    (fun i => (Sum.inl (Sum.inr i) : StoppedSpectralVariable k)) (augmentedOrbitEntryPolynomial k r j)
  have hg := polynomialSingularValueGraph_definable A (MvPolynomial.X (Sum.inr ())) 3
  have hs := (stoppedStateFamily_definable k).preimage_comp
    (Sum.inl : StoppedStateVariable k → StoppedSpectralVariable k)
  convert hs.inter hg using 1
  ext v
  simp only [stoppedAugmentedFourthFamily, stoppedStateFamily, Set.mem_setOf_eq,
    Set.mem_inter_iff, Set.mem_preimage, Function.comp_def, A,
    MvPolynomial.eval_X, MvPolynomial.eval_rename,
    eval_augmentedOrbitEntryPolynomial_coordinates, augmentedOrbitSingularValues, and_assoc]

theorem stoppedNormalLeast_fixed_formula (k : ℕ) :
    ∃ (C : Finset ℝ) (φ : Language.ring[[(C : Set ℝ)]].Formula (StoppedSpectralVariable k)),
      ∀ (P : ℝ) (S : AugmentedState k) (t : ℝ),
        φ.Realize (stoppedSpectralCoordinates P S t) ↔
          2 ≤ P ∧ AugmentedTranslationStopped P S ∧ t = normalOrbitSingularValues k S 2 := by
  obtain ⟨C, _, φ, hφ⟩ := Set.definable_iff_finitely_definable.mp
    (stoppedNormalLeastFamily_definable k)
  refine ⟨C, φ, ?_⟩
  intro P S t
  have h : stoppedSpectralCoordinates P S t ∈ stoppedNormalLeastFamily k ↔
      2 ≤ P ∧ AugmentedTranslationStopped P S ∧ t = normalOrbitSingularValues k S 2 := by
    simp [stoppedNormalLeastFamily, stoppedSpectralCoordinates, stoppedStateCoordinates]
  rwa [hφ] at h

theorem stoppedAugmentedFourth_fixed_formula (k : ℕ) :
    ∃ (C : Finset ℝ) (φ : Language.ring[[(C : Set ℝ)]].Formula (StoppedSpectralVariable k)),
      ∀ (P : ℝ) (S : AugmentedState k) (t : ℝ),
        φ.Realize (stoppedSpectralCoordinates P S t) ↔
          2 ≤ P ∧ AugmentedTranslationStopped P S ∧ t = augmentedOrbitSingularValues k S 3 := by
  obtain ⟨C, _, φ, hφ⟩ := Set.definable_iff_finitely_definable.mp
    (stoppedAugmentedFourthFamily_definable k)
  refine ⟨C, φ, ?_⟩
  intro P S t
  have h : stoppedSpectralCoordinates P S t ∈ stoppedAugmentedFourthFamily k ↔
      2 ≤ P ∧ AugmentedTranslationStopped P S ∧ t = augmentedOrbitSingularValues k S 3 := by
    simp [stoppedAugmentedFourthFamily, stoppedSpectralCoordinates, stoppedStateCoordinates]
  rwa [hφ] at h

end PaperI
