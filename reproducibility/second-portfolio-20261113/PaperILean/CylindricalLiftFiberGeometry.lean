import PaperILean.CylindricalLiftSection
import Mathlib.Order.UpperLower.Basic

/-! Actual scalar fibers of the existing cylindrical lifts. The base-membership
premise is retained, and boundary continuity is used only on its stated cell.
These are local details of I1261, not a replacement dimension theorem. -/
noncomputable section
namespace PaperI
open Set

def CylindricalLift.IsGraph {α : Type} {U : Set (α → ℝ)}
    (c : CylindricalLift U) : Prop :=
  match c with
  | .graph _ => True
  | _ => False

def CylindricalLift.scalarFiber {α : Type} {U : Set (α → ℝ)}
    (c : CylindricalLift U) (p : α → ℝ) : Set ℝ :=
  {t | Sum.elim p (fun _ : Unit => t) ∈ c.region}

theorem continuous_cadScalarInsert {α : Type} (p : α → ℝ) :
    Continuous (fun t : ℝ => Sum.elim p (fun _ : Unit => t)) := by
  apply continuous_pi
  intro i
  cases i with
  | inl i => exact continuous_const
  | inr i => exact continuous_id

theorem CylindricalLift.scalarFiber_eq_empty_of_not_mem {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) {p : α → ℝ} (hp : p ∉ U) :
    c.scalarFiber p = ∅ := by
  apply subset_empty_iff.mp
  intro t ht
  exact (hp ht.1).elim

theorem CylindricalLift.scalarFiber_nonempty {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) {p : α → ℝ} (hp : p ∈ U) :
    (c.scalarFiber p).Nonempty :=
  ⟨c.sample p, c.sectionMap_mem hp⟩

theorem CylindricalLift.scalarFiber_eq_singleton_of_isGraph {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) {p : α → ℝ}
    (hp : p ∈ U) (hg : c.IsGraph) : c.scalarFiber p = {c.sample p} := by
  cases c <;> simp_all [IsGraph, scalarFiber, region, sample]

theorem CylindricalLift.scalarFiber_cases {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) {p : α → ℝ} (hp : p ∈ U) :
    (∃ a, c.IsGraph ∧ c.scalarFiber p = {a}) ∨
      (∃ a b, a < b ∧ c.scalarFiber p = Ioo a b) ∨
      (∃ a, c.scalarFiber p = Ioi a) ∨
      (∃ b, c.scalarFiber p = Iio b) ∨ c.scalarFiber p = univ := by
  cases c with
  | graph f =>
    left
    exact ⟨f.value p, trivial, by ext t; simp [scalarFiber, region, hp]⟩
  | between l u h =>
    exact Or.inr (Or.inl ⟨l.value p, u.value p, h p hp,
      by ext t; simp [scalarFiber, region, hp]⟩)
  | above l =>
    exact Or.inr (Or.inr (Or.inl ⟨l.value p, by ext t; simp [scalarFiber, region, hp]⟩))
  | below u =>
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u.value p, by ext t; simp [scalarFiber, region, hp]⟩)))
  | whole =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (by ext t; simp [scalarFiber, region, hp]))))

theorem CylindricalLift.scalarFiber_ordConnected {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) (p : α → ℝ) :
    OrdConnected (c.scalarFiber p) := by
  by_cases hp : p ∈ U
  · rcases c.scalarFiber_cases hp with ⟨a, _, h⟩ | ⟨a,b,_,h⟩ | ⟨a,h⟩ | ⟨b,h⟩ | h
    · rw [h]; exact ordConnected_singleton
    · rw [h]; exact ordConnected_Ioo
    · rw [h]; exact ordConnected_Ioi
    · rw [h]; exact ordConnected_Iio
    · rw [h]; exact ordConnected_univ
  · rw [c.scalarFiber_eq_empty_of_not_mem hp]
    exact ordConnected_empty

theorem CylindricalLift.scalarFiber_isOpen_of_not_isGraph {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) (p : α → ℝ) (hg : ¬ c.IsGraph) :
    IsOpen (c.scalarFiber p) := by
  by_cases hp : p ∈ U
  · rcases c.scalarFiber_cases hp with ⟨a, hgraph, _⟩ | ⟨a,b,_,h⟩ | ⟨a,h⟩ | ⟨b,h⟩ | h
    · exact (hg hgraph).elim
    · rw [h]; exact isOpen_Ioo
    · rw [h]; exact isOpen_Ioi
    · rw [h]; exact isOpen_Iio
    · rw [h]; exact isOpen_univ
  · rw [c.scalarFiber_eq_empty_of_not_mem hp]
    exact isOpen_empty

theorem CylindricalLift.bounded_scalarFiber_cases {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) {p : α → ℝ} (hp : p ∈ U)
    (hlo : BddBelow (c.scalarFiber p)) (hhi : BddAbove (c.scalarFiber p)) :
    (∃ a, c.IsGraph ∧ c.scalarFiber p = {a}) ∨
      ∃ a b, a < b ∧ c.scalarFiber p = Ioo a b := by
  rcases c.scalarFiber_cases hp with h | h | ⟨a,h⟩ | ⟨b,h⟩ | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (not_bddAbove_Ioi a (h ▸ hhi)).elim
  · exact (not_bddBelow_Iio b (h ▸ hlo)).elim
  · exact (not_bddAbove_univ (h ▸ hhi)).elim

theorem CylindricalBoundary.continuousOn_scalarFiber {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U)
    (f : CylindricalBoundary c.region) (p : α → ℝ) :
    ContinuousOn (fun t => f.value (Sum.elim p (fun _ : Unit => t))) (c.scalarFiber p) :=
  f.continuousOn.comp (continuous_cadScalarInsert p).continuousOn (fun _ ht => ht)

end PaperI
