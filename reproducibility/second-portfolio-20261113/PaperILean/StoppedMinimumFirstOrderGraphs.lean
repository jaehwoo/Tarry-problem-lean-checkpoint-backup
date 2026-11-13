import PaperILean.AttainedMinimumDefinability
import PaperILean.StoppedSpectralMinimum
import PaperILean.StoppedOrbitFirstOrderGraphs

/-! I625-638, I683 and I693: exact fixed formulas for the attained normal-least
and full-fourth minimum functions on P>=2. This closes the minimum-graph
interface, but does not implement real quantifier elimination or growth. -/

noncomputable section
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def minimumParameterCoordinates (P t : ℝ) : Unit ⊕ Unit → ℝ :=
  Sum.elim (fun _ => P) (fun _ => t)

theorem stoppedNormal_attained_graph_iff (k : ℕ) (P t : ℝ) :
    minimumParameterCoordinates P t ∈ attainedFiberMinimumGraph (stoppedNormalLeastFamily k) ↔
      2 ≤ P ∧ t = stoppedNormalMinimum k P := by
  have h := attainedFiberMinimumGraph_function_iff
    (fun (p : Unit → ℝ) (x : AugmentedCoordinateIndex k → ℝ) =>
      2 ≤ p () ∧ AugmentedTranslationStopped (p ()) ((augmentedStateCoordinates k).symm x))
    (fun (p : Unit → ℝ) (x : AugmentedCoordinateIndex k → ℝ) =>
      normalOrbitSingularValues k ((augmentedStateCoordinates k).symm x) 2)
    (fun _ => P) t
  simp only [and_assoc] at h
  change (minimumParameterCoordinates P t ∈ attainedFiberMinimumGraph (stoppedNormalLeastFamily k) ↔ _) at h
  rw [h]
  constructor
  · rintro ⟨x, hP, hx, ht, hmin⟩
    refine ⟨hP, (stoppedNormalMinimum_eq_iff k P t hP).mpr
      ⟨(augmentedStateCoordinates k).symm x, hx, ht, ?_⟩⟩
    intro T hT
    simpa using hmin ((augmentedStateCoordinates k) T) ⟨hP, by simpa using hT⟩
  · rintro ⟨hP, ht⟩
    obtain ⟨S, hS, he, hmin⟩ := (stoppedNormalMinimum_eq_iff k P t hP).mp ht
    refine ⟨(augmentedStateCoordinates k) S, hP, by simpa using hS,
      by simpa using he, ?_⟩
    intro y hy
    exact hmin ((augmentedStateCoordinates k).symm y) hy.2

theorem stoppedFourth_attained_graph_iff (k : ℕ) (P t : ℝ) :
    minimumParameterCoordinates P t ∈ attainedFiberMinimumGraph (stoppedAugmentedFourthFamily k) ↔
      2 ≤ P ∧ t = stoppedFourthMinimum k P := by
  have h := attainedFiberMinimumGraph_function_iff
    (fun (p : Unit → ℝ) (x : AugmentedCoordinateIndex k → ℝ) =>
      2 ≤ p () ∧ AugmentedTranslationStopped (p ()) ((augmentedStateCoordinates k).symm x))
    (fun (p : Unit → ℝ) (x : AugmentedCoordinateIndex k → ℝ) =>
      augmentedOrbitSingularValues k ((augmentedStateCoordinates k).symm x) 3)
    (fun _ => P) t
  simp only [and_assoc] at h
  change (minimumParameterCoordinates P t ∈ attainedFiberMinimumGraph (stoppedAugmentedFourthFamily k) ↔ _) at h
  rw [h]
  constructor
  · rintro ⟨x, hP, hx, ht, hmin⟩
    refine ⟨hP, (stoppedFourthMinimum_eq_iff k P t hP).mpr
      ⟨(augmentedStateCoordinates k).symm x, hx, ht, ?_⟩⟩
    intro T hT
    simpa using hmin ((augmentedStateCoordinates k) T) ⟨hP, by simpa using hT⟩
  · rintro ⟨hP, ht⟩
    obtain ⟨S, hS, he, hmin⟩ := (stoppedFourthMinimum_eq_iff k P t hP).mp ht
    refine ⟨(augmentedStateCoordinates k) S, hP, by simpa using hS,
      by simpa using he, ?_⟩
    intro y hy
    exact hmin ((augmentedStateCoordinates k).symm y) hy.2

theorem minimumParameterCoordinates_eta (v : Unit ⊕ Unit → ℝ) :
    minimumParameterCoordinates (v (Sum.inl ())) (v (Sum.inr ())) = v := by
  funext a
  rcases a with ⟨⟩ | ⟨⟩ <;> rfl

theorem stoppedNormalMinimum_graph_definable (k : ℕ) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedNormalMinimum k (v (Sum.inl ()))} := by
  convert attainedFiberMinimumGraph_definable (stoppedNormalLeastFamily_definable k) using 1
  ext v
  simpa only [minimumParameterCoordinates_eta, Set.mem_setOf_eq] using
    (stoppedNormal_attained_graph_iff k (v (Sum.inl ())) (v (Sum.inr ()))).symm

theorem stoppedFourthMinimum_graph_definable (k : ℕ) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedFourthMinimum k (v (Sum.inl ()))} := by
  convert attainedFiberMinimumGraph_definable (stoppedAugmentedFourthFamily_definable k) using 1
  ext v
  simpa only [minimumParameterCoordinates_eta, Set.mem_setOf_eq] using
    (stoppedFourth_attained_graph_iff k (v (Sum.inl ())) (v (Sum.inr ()))).symm

theorem stoppedNormalMinimum_fixed_formula (k : ℕ) :
    ∃ (C : Finset ℝ) (φ : Language.ring[[(C : Set ℝ)]].Formula (Unit ⊕ Unit)),
      ∀ P t : ℝ, φ.Realize (minimumParameterCoordinates P t) ↔
        2 ≤ P ∧ t = stoppedNormalMinimum k P := by
  obtain ⟨C, _, φ, hφ⟩ := Set.definable_iff_finitely_definable.mp
    (stoppedNormalMinimum_graph_definable k)
  refine ⟨C, φ, ?_⟩
  intro P t
  have h : minimumParameterCoordinates P t ∈
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedNormalMinimum k (v (Sum.inl ()))} ↔
      2 ≤ P ∧ t = stoppedNormalMinimum k P := by rfl
  rwa [hφ] at h

theorem stoppedFourthMinimum_fixed_formula (k : ℕ) :
    ∃ (C : Finset ℝ) (φ : Language.ring[[(C : Set ℝ)]].Formula (Unit ⊕ Unit)),
      ∀ P t : ℝ, φ.Realize (minimumParameterCoordinates P t) ↔
        2 ≤ P ∧ t = stoppedFourthMinimum k P := by
  obtain ⟨C, _, φ, hφ⟩ := Set.definable_iff_finitely_definable.mp
    (stoppedFourthMinimum_graph_definable k)
  refine ⟨C, φ, ?_⟩
  intro P t
  have h : minimumParameterCoordinates P t ∈
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedFourthMinimum k (v (Sum.inl ()))} ↔
      2 ≤ P ∧ t = stoppedFourthMinimum k P := by rfl
  rwa [hφ] at h

end PaperI
