import PaperILean.AugmentedOrbitEuclidean
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! I595-607, I625-638, I683 and I693: the exact stopped windows are closed
and compact; matrix entries vary continuously. No uniform P-power estimate
or semialgebraic classification is asserted. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

/-- The inherited differential, now viewed as a linear function of the state.
No coefficient or physical entry is discarded beyond the inherited definition. -/
def augmentedOrbitStateMap (k : ℕ) (ξ : Fin 6 → ℝ) :
    AugmentedState k →ₗ[ℝ] AugmentedState k where
  toFun S := augmentedOrbitDifferential k S ξ
  map_add' S T := by
    simp [augmentedOrbitDifferential, physicalAffineFieldAction, map_add,
      Matrix.add_mulVec, add_mul]
  map_smul' r S := by
    simp [augmentedOrbitDifferential, physicalAffineFieldAction, map_smul,
      Matrix.smul_mulVec_assoc, smul_mul_assoc]

theorem continuous_augmentedOrbit_state (k : ℕ) (ξ : Fin 6 → ℝ) :
    Continuous (fun S : AugmentedState k => augmentedOrbitDifferential k S ξ) :=
  (augmentedOrbitStateMap k ξ).continuous_of_finiteDimensional

theorem continuous_augmentedStateNorm (k : ℕ) :
    Continuous (augmentedStateNorm : AugmentedState k → ℝ) := by
  exact (augmentedStateEuclideanCoordinates k).toLinearMap.continuous_of_finiteDimensional.norm.congr
    (fun S => augmentedStateEuclideanCoordinates_norm S)

theorem isCompact_augmentedStateNorm_sublevel (k : ℕ) (P : ℝ) :
    IsCompact {S : AugmentedState k | augmentedStateNorm S ≤ P} := by
  let e := (augmentedStateEuclideanCoordinates k).toContinuousLinearEquiv.toHomeomorph
  have h := e.isCompact_preimage.mpr (isCompact_closedBall (0 : EuclideanSpace ℝ (AugmentedCoordinateIndex k)) P)
  change IsCompact {S : AugmentedState k | ‖augmentedStateEuclideanCoordinates k S - 0‖ ≤ P} at h
  simpa only [sub_zero, augmentedStateEuclideanCoordinates_norm] using h

theorem isClosed_augmentedTranslationStopped (k : ℕ) (P : ℝ) :
    IsClosed {S : AugmentedState k | AugmentedTranslationStopped P S} := by
  simp_rw [augmentedTranslationStopped_iff_orbit]
  apply IsClosed.inter (isClosed_le (continuous_augmentedStateNorm k) continuous_const)
  change IsClosed {S : AugmentedState k | ∀ h : PhysicalSpace,
    P ^ (-2 : ℤ) * physicalEuclideanNorm h ^ 2 ≤
      augmentedStateNorm (augmentedOrbitDifferential k S (upperAffineTranslationCoordinates h)) ^ 2}
  rw [Set.setOf_forall]
  exact isClosed_iInter fun h => isClosed_le continuous_const
    (((continuous_augmentedStateNorm k).comp
      (continuous_augmentedOrbit_state k (upperAffineTranslationCoordinates h))).pow 2)

theorem isCompact_augmentedTranslationStopped (k : ℕ) (P : ℝ) :
    IsCompact {S : AugmentedState k | AugmentedTranslationStopped P S} := by
  exact (isCompact_augmentedStateNorm_sublevel k P).of_isClosed_subset
    (isClosed_augmentedTranslationStopped k P) (fun _ h => h.1)
/-- The lower parameter cutoff is the source convention; no invertibility of M
is imposed. At P=0 the inverse-square expression need not be continuous. -/
theorem isClosed_augmentedStoppedParameterFamily (k : ℕ) :
    IsClosed {z : ℝ × AugmentedState k | 2 ≤ z.1 ∧
      AugmentedTranslationStopped z.1 z.2} := by
  have hbase : IsClosed {z : ℝ × AugmentedState k | (2 : ℝ) ≤ z.1} :=
    isClosed_le continuous_const continuous_fst
  have hpow : ContinuousOn (fun z : ℝ × AugmentedState k => z.1 ^ (-2 : ℤ))
      {z | (2 : ℝ) ≤ z.1} :=
    continuous_fst.continuousOn.zpow₀ _ (fun z hz => Or.inl (by dsimp at hz; linarith))
  have hineq (h : PhysicalSpace) : IsClosed {z : ℝ × AugmentedState k |
      2 ≤ z.1 ∧ z.1 ^ (-2 : ℤ) * physicalEuclideanNorm h ^ 2 ≤
        augmentedStateNorm (augmentedOrbitDifferential k z.2
          (upperAffineTranslationCoordinates h)) ^ 2} :=
    hbase.isClosed_le (hpow.mul continuousOn_const)
      ((((continuous_augmentedStateNorm k).comp
        (continuous_augmentedOrbit_state k (upperAffineTranslationCoordinates h))).comp
          continuous_snd).pow 2).continuousOn
  have hwindow : IsClosed {z : ℝ × AugmentedState k |
      2 ≤ z.1 ∧ augmentedStateNorm z.2 ≤ z.1} :=
    hbase.inter (isClosed_le ((continuous_augmentedStateNorm k).comp continuous_snd)
      continuous_fst)
  have h := hwindow.inter (isClosed_iInter hineq)
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
    augmentedTranslationStopped_iff_orbit]
  constructor
  · rintro ⟨hP, hnorm, hall⟩
    exact ⟨⟨hP, hnorm⟩, fun u => ⟨hP, hall u⟩⟩
  · rintro ⟨⟨hP, hnorm⟩, hall⟩
    exact ⟨hP, hnorm, fun u => (hall u).2⟩

theorem isClosed_augmentedStoppedBoundedFamily (k : ℕ) (P₀ : ℝ) :
    IsClosed {z : ℝ × AugmentedState k | 2 ≤ z.1 ∧ z.1 ≤ P₀ ∧
      AugmentedTranslationStopped z.1 z.2} := by
  have h := (isClosed_augmentedStoppedParameterFamily k).inter
    (isClosed_le continuous_fst (continuous_const : Continuous (fun _ : ℝ × AugmentedState k => P₀)))
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  tauto

theorem isCompact_augmentedStoppedBoundedFamily (k : ℕ) (P₀ : ℝ) :
    IsCompact {z : ℝ × AugmentedState k | 2 ≤ z.1 ∧ z.1 ≤ P₀ ∧
      AugmentedTranslationStopped z.1 z.2} := by
  apply ((isCompact_Icc : IsCompact (Set.Icc (2 : ℝ) P₀)).prod
    (isCompact_augmentedStateNorm_sublevel k P₀)).of_isClosed_subset
      (isClosed_augmentedStoppedBoundedFamily k P₀)
  intro z hz
  exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2.1.trans hz.2.1⟩

theorem continuous_augmentedOrbitMatrix (k : ℕ) :
    Continuous (augmentedOrbitMatrix k) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp_rw [augmentedOrbitMatrix_column]
  exact (continuous_apply i).comp
    ((augmentedStateCoordinates k).toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_augmentedOrbit_state k (Pi.single j 1)))

theorem continuous_normalOrbitMatrix (k : ℕ) :
    Continuous (normalOrbitMatrix k) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp_rw [normalOrbitMatrix_first_three]
  exact ((continuous_apply (j.castLE (by decide))).comp (continuous_apply i)).comp
    (continuous_augmentedOrbitMatrix k)

end PaperI
