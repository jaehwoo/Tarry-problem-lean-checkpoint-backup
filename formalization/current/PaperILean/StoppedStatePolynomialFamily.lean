import PaperILean.AugmentedOrbitStatePolynomials
import PaperILean.RealPolynomialDefinability
import PaperILean.StoppedOrbitAlgebraicCertificates

/-! I595-607 and I625: a fixed real first-order formula for the actual stopped
family, with P as a free parameter and all three direction coordinates bound.
This proves definability, not quantifier elimination or uniform conditioning. -/

noncomputable section
open scoped Matrix BigOperators
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

abbrev StoppedStateVariable (k : ℕ) := Unit ⊕ AugmentedCoordinateIndex k

def stoppedStateCoordinates {k : ℕ} (P : ℝ) (S : AugmentedState k) :
    StoppedStateVariable k → ℝ :=
  Sum.elim (fun _ => P) (augmentedStateCoordinates k S)

def stoppedParameterPolynomial (k : ℕ) : MvPolynomial (StoppedStateVariable k) ℝ :=
  MvPolynomial.X (Sum.inl ()) - MvPolynomial.C 2

def stoppedWindowPolynomial (k : ℕ) : MvPolynomial (StoppedStateVariable k) ℝ :=
  MvPolynomial.X (Sum.inl ()) ^ 2 -
    ∑ r : AugmentedCoordinateIndex k, MvPolynomial.X (Sum.inr r) ^ 2

def translationImagePolynomial (k : ℕ) (r : AugmentedCoordinateIndex k) :
    MvPolynomial (StoppedStateVariable k ⊕ Fin 3) ℝ :=
  ∑ j : Fin 6,
    MvPolynomial.rename (fun i => Sum.inl (Sum.inr i)) (augmentedOrbitEntryPolynomial k r j) *
      MvPolynomial.rename Sum.inr (linearCoordinatePolynomial upperAffineTranslationCoordinates j)

def stoppedTranslationPolynomial (k : ℕ) :
    MvPolynomial (StoppedStateVariable k ⊕ Fin 3) ℝ :=
  MvPolynomial.X (Sum.inl (Sum.inl ())) ^ 2 *
    (∑ r : AugmentedCoordinateIndex k, translationImagePolynomial k r ^ 2) -
      ∑ i : Fin 3, MvPolynomial.X (Sum.inr i) ^ 2

theorem eval_stoppedParameterPolynomial {k : ℕ} (P : ℝ) (S : AugmentedState k) :
    MvPolynomial.eval (stoppedStateCoordinates P S) (stoppedParameterPolynomial k) = P - 2 := by
  simp [stoppedParameterPolynomial, stoppedStateCoordinates]

theorem eval_stoppedWindowPolynomial {k : ℕ} (P : ℝ) (S : AugmentedState k) :
    MvPolynomial.eval (stoppedStateCoordinates P S) (stoppedWindowPolynomial k) =
      P ^ 2 - ∑ r, (augmentedStateCoordinates k S r) ^ 2 := by
  simp [stoppedWindowPolynomial, stoppedStateCoordinates, MvPolynomial.eval_sum]

theorem eval_translationImagePolynomial {k : ℕ} (P : ℝ) (S : AugmentedState k)
    (h : PhysicalSpace) (r : AugmentedCoordinateIndex k) :
    MvPolynomial.eval (Sum.elim (stoppedStateCoordinates P S) h)
      (translationImagePolynomial k r) =
        (augmentedOrbitMatrix k S *ᵥ upperAffineTranslationCoordinates h) r := by
  simp [translationImagePolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_rename,
    Function.comp_def, stoppedStateCoordinates, eval_augmentedOrbitEntryPolynomial,
    eval_linearCoordinatePolynomial, Matrix.mulVec, dotProduct]

theorem eval_stoppedTranslationPolynomial {k : ℕ} (P : ℝ) (S : AugmentedState k)
    (h : PhysicalSpace) :
    MvPolynomial.eval (Sum.elim (stoppedStateCoordinates P S) h)
      (stoppedTranslationPolynomial k) =
        P ^ 2 * ∑ r, ((augmentedOrbitMatrix k S *ᵥ upperAffineTranslationCoordinates h) r) ^ 2 -
          ∑ i, h i ^ 2 := by
  simp only [stoppedTranslationPolynomial, map_sub, map_mul, map_pow,
    MvPolynomial.eval_sum, eval_translationImagePolynomial, MvPolynomial.eval_X,
    Sum.elim_inl, Sum.elim_inr]
  rfl

theorem stoppedWindowPolynomial_degree (k : ℕ) :
    (stoppedWindowPolynomial k).totalDegree ≤ 2 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp [MvPolynomial.totalDegree_X_pow]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro r hr
    simp [MvPolynomial.totalDegree_X_pow]

theorem translationImagePolynomial_degree (k : ℕ) (r : AugmentedCoordinateIndex k) :
    (translationImagePolynomial k r).totalDegree ≤ 2 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  exact Nat.add_le_add
    ((MvPolynomial.totalDegree_rename_le _ _).trans (augmentedOrbitEntryPolynomial_degree k r j))
    ((MvPolynomial.totalDegree_rename_le _ _).trans
      (linearCoordinatePolynomial_degree upperAffineTranslationCoordinates j))

theorem stoppedTranslationPolynomial_degree (k : ℕ) :
    (stoppedTranslationPolynomial k).totalDegree ≤ 6 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    have h4 : (∑ r : AugmentedCoordinateIndex k, translationImagePolynomial k r ^ 2).totalDegree ≤ 4 := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro r hr
      exact (MvPolynomial.totalDegree_pow _ _).trans
        (Nat.mul_le_mul_left 2 (translationImagePolynomial_degree k r))
    simpa [MvPolynomial.totalDegree_X_pow] using Nat.add_le_add_left h4 2
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    simp [MvPolynomial.totalDegree_X_pow]

theorem stoppedFamily_iff_polynomial_conditions {k : ℕ} (P : ℝ) (S : AugmentedState k) :
    (2 ≤ P ∧ AugmentedTranslationStopped P S) ↔
      0 ≤ MvPolynomial.eval (stoppedStateCoordinates P S) (stoppedParameterPolynomial k) ∧
      0 ≤ MvPolynomial.eval (stoppedStateCoordinates P S) (stoppedWindowPolynomial k) ∧
      ∀ h : PhysicalSpace, 0 ≤ MvPolynomial.eval (Sum.elim (stoppedStateCoordinates P S) h)
        (stoppedTranslationPolynomial k) := by
  simp only [eval_stoppedParameterPolynomial, eval_stoppedWindowPolynomial,
    eval_stoppedTranslationPolynomial, sub_nonneg]
  by_cases hP : 2 ≤ P
  · rw [augmentedTranslationStopped_iff_squared hP]
    rfl
  · simp [hP]

def stoppedStateFamily (k : ℕ) : Set (StoppedStateVariable k → ℝ) :=
  {v | 2 ≤ v (Sum.inl ()) ∧ AugmentedTranslationStopped (v (Sum.inl ()))
    ((augmentedStateCoordinates k).symm (fun r => v (Sum.inr r)))}

theorem stoppedStateFamily_definable (k : ℕ) :
    (Set.univ : Set ℝ).Definable Language.ring (stoppedStateFamily k) := by
  have h := (realPolynomial_nonneg_definable (stoppedParameterPolynomial k)).inter
    ((realPolynomial_nonneg_definable (stoppedWindowPolynomial k)).inter
      (realDefinable_forall (realPolynomial_nonneg_definable (stoppedTranslationPolynomial k))))
  convert h using 1
  ext v
  have he : stoppedStateCoordinates (v (Sum.inl ()))
      ((augmentedStateCoordinates k).symm (fun r => v (Sum.inr r))) = v := by
    funext a
    cases a with
    | inl u => cases u; rfl
    | inr r => simp [stoppedStateCoordinates]
  simpa only [stoppedStateFamily, Set.mem_setOf_eq, Set.mem_inter_iff, he]
    using stoppedFamily_iff_polynomial_conditions (v (Sum.inl ()))
      ((augmentedStateCoordinates k).symm (fun r => v (Sum.inr r)))

/-- All real constants can be chosen once for each k, before every P and state.
This is finite first-order definability, not an effective formula-size bound. -/
theorem stoppedStateFamily_finitely_definable (k : ℕ) :
    ∃ C : Finset ℝ, (C : Set ℝ).Definable Language.ring (stoppedStateFamily k) := by
  obtain ⟨C, _, hC⟩ := Set.definable_iff_finitely_definable.mp
    (stoppedStateFamily_definable k)
  exact ⟨C, hC⟩

end PaperI
