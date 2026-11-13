import PaperILean.OriginalJointBufferedComponents
import PaperILean.PriorityAssignment

/-! I1259/I1265: Borel membership for original labels at a fixed distance
scale, and multiplicity controlled by actual components, not labels. The
coefficient/scale map is common to all labels. -/

noncomputable section
namespace PaperI
open Set

def componentAssignedLabel {Ω Λ ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : JointComponentPartition A)
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (point : Ω → Λ → κ → ℝ)
    (ω : Ω) (j : Λ) (i : Fin D.count) : Prop :=
  active ω j ∧ point ω j ∈ projectionFiber (D.part i) (param ω)

theorem componentAssignedLabel_unique {Ω Λ ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : JointComponentPartition A)
    {active : Ω → Λ → Prop} {param : Ω → ρ → ℝ} {point : Ω → Λ → κ → ℝ}
    {ω : Ω} {j : Λ} {i k : Fin D.count}
    (hi : componentAssignedLabel D active param point ω j i)
    (hk : componentAssignedLabel D active param point ω j k) : i = k := by
  by_contra h
  exact (disjoint_left.mp (D.disjoint (param ω) h)) hi.2 hk.2

theorem componentAssignedLabel_exists_unique_iff {Ω Λ ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : JointComponentPartition A)
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (point : Ω → Λ → κ → ℝ)
    (hmem : ∀ ω j, active ω j → point ω j ∈ projectionFiber A (param ω))
    (ω : Ω) (j : Λ) :
    (∃! i, componentAssignedLabel D active param point ω j i) ↔ active ω j := by
  constructor
  · rintro ⟨i,hi,_⟩
    exact hi.1
  · intro hj
    obtain ⟨i,hi⟩ := D.cover (param ω) (point ω j) (hmem ω j hj)
    exact ⟨i,⟨hj,hi⟩,fun k hk => componentAssignedLabel_unique D hk ⟨hj,hi⟩⟩

theorem componentAssignedLabel_firstEligible_iff {Ω Λ ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : JointComponentPartition A)
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (point : Ω → Λ → κ → ℝ)
    (rank : Fin D.count → ℕ) (ω : Ω) (j : Λ) (i : Fin D.count) :
    FirstEligible rank (componentAssignedLabel D active param point) ω j i ↔
      componentAssignedLabel D active param point ω j i := by
  refine ⟨And.left,fun hi => ⟨hi,?_⟩⟩
  intro k hk he
  have hki := componentAssignedLabel_unique D he hi
  exact (lt_irrefl (rank i)) (hki ▸ hk)

theorem componentAssignedLabel_disjoint {Ω Λ ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : JointComponentPartition A)
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (point : Ω → Λ → κ → ℝ)
    (ω : Ω) : Pairwise (fun i k : Fin D.count =>
      Disjoint {j | componentAssignedLabel D active param point ω j i}
        {j | componentAssignedLabel D active param point ω j k}) := by
  intro i k hik
  rw [disjoint_left]
  exact fun _ hi hk => hik (componentAssignedLabel_unique D hi hk)

theorem componentAssignedLabel_component {Ω Λ ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : JointComponentPartition A)
    {active : Ω → Λ → Prop} {param : Ω → ρ → ℝ} {point : Ω → Λ → κ → ℝ}
    {ω : Ω} {j : Λ} {i : Fin D.count}
    (hi : componentAssignedLabel D active param point ω j i) :
    projectionFiber (D.part i) (param ω) =
      connectedComponentIn (projectionFiber A (param ω)) (point ω j) :=
  D.component (param ω) i (point ω j) hi.2

theorem measurableSet_componentAssignedLabel {Ω Λ ρ κ : Type*}
    [MeasurableSpace Ω] [Finite ρ] [Finite κ]
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : JointComponentPartition A)
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (point : Ω → Λ → κ → ℝ)
    (ha : ∀ j, MeasurableSet {ω | active ω j})
    (hp : Measurable param) (hx : ∀ j, Measurable (fun ω => point ω j))
    (j : Λ) (i : Fin D.count) :
    MeasurableSet {ω | componentAssignedLabel D active param point ω j i} := by
  have hv : Measurable (fun ω => Sum.elim (param ω) (point ω j)) := by
    apply measurable_pi_lambda
    intro q
    cases q with
    | inl r => exact (measurable_pi_apply r).comp hp
    | inr k => exact (measurable_pi_apply k).comp (hx j)
  have hpart : MeasurableSet (D.part i) := by
    simpa only [← BorelSpace.measurable_eq] using hasPolynomialSignDescription_borel (D.semialgebraic i)
  exact (ha j).inter (hpart.preimage hv)

theorem measurableSet_componentFirstAssignment {Ω Λ ρ κ : Type*}
    [MeasurableSpace Ω] [Finite ρ] [Finite κ]
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : JointComponentPartition A)
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (point : Ω → Λ → κ → ℝ)
    (ha : ∀ j, MeasurableSet {ω | active ω j})
    (hp : Measurable param) (hx : ∀ j, Measurable (fun ω => point ω j))
    (j : Λ) (i : Fin D.count) :
    MeasurableSet {ω | FirstEligible (countablePieceRank (Fin D.count))
      (componentAssignedLabel D active param point) ω j i} :=
  measurableSet_firstEligible _ _ (measurableSet_componentAssignedLabel D active param point ha hp hx) j i

theorem componentAssignedLabel_count_le_components {Ω Λ ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : JointComponentPartition A)
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (point : Ω → Λ → κ → ℝ)
    (ω : Ω) :
    Nat.card {i : Fin D.count // ∃ j, componentAssignedLabel D active param point ω j i} ≤
      Nat.card (ConnectedComponents (projectionFiber A (param ω))) := by
  rw [← D.active_count_eq_components]
  let f : {i : Fin D.count // ∃ j, componentAssignedLabel D active param point ω j i} →
      {i : Fin D.count // (projectionFiber (D.part i) (param ω)).Nonempty} := fun i =>
    ⟨i.val,by obtain ⟨j,hj⟩ := i.property; exact ⟨point ω j,hj.2⟩⟩
  apply Nat.card_le_card_of_injective f
  intro i k hik
  apply Subtype.ext
  exact congrArg (fun t : {i : Fin D.count //
    (projectionFiber (D.part i) (param ω)).Nonempty} => t.val) hik

theorem componentAssignedLabel_count_le {Ω Λ ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : JointComponentPartition A)
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (point : Ω → Λ → κ → ℝ)
    (ω : Ω) :
    Nat.card {i : Fin D.count // ∃ j, componentAssignedLabel D active param point ω j i} ≤ D.count :=
  (componentAssignedLabel_count_le_components D active param point ω).trans
    (D.component_count_le (param ω))

end PaperI
