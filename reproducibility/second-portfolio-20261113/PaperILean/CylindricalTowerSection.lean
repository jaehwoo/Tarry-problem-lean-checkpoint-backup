import PaperILean.CylindricalLiftSection

/-! Recursive section of a supplied cylindrical cell over its base. The base
coordinates are preserved exactly. Region definability is retained as part of
the structural cell data, not inferred from separate parameterwise choices.
This file does not assert existence of an adapted CAD for an arbitrary input. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def CADVariables (α : Type) : ℕ → Type
  | 0 => α
  | n+1 => CADVariables α n ⊕ Unit

instance cadVariables_finite {α : Type} [Finite α] (n : ℕ) : Finite (CADVariables α n) := by
  induction n with
  | zero => exact inferInstanceAs (Finite α)
  | succ n ih => exact inferInstanceAs (Finite (CADVariables α n ⊕ Unit))

def cadBaseCoordinate {α : Type} : (n : ℕ) → α → CADVariables α n
  | 0 => id
  | n+1 => Sum.inl ∘ cadBaseCoordinate n

inductive CylindricalTower {α : Type} (U : Set (α → ℝ)) :
    {n : ℕ} → Set (CADVariables α n → ℝ) → Type where
  | base : CylindricalTower U (n := 0) U
  | step {n : ℕ} {S : Set (CADVariables α n → ℝ)}
      (previous : CylindricalTower U S) (lift : CylindricalLift S)
      (region_definable : (univ : Set ℝ).Definable Language.ring lift.region) :
      CylindricalTower U (n := n+1) lift.region

def CylindricalTower.sectionMap {α : Type} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S) :
    (α → ℝ) → CADVariables α n → ℝ := by
  induction c with
  | base => exact id
  | step previous lift _ ih => exact lift.sectionMap ∘ ih

theorem CylindricalTower.region_definable {α : Type} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S)
    (hU : (univ : Set ℝ).Definable Language.ring U) :
    (univ : Set ℝ).Definable Language.ring S := by
  cases c with
  | base => exact hU
  | step _ _ h => exact h

theorem CylindricalTower.sectionMap_mem {α : Type} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S)
    {x : α → ℝ} (hx : x ∈ U) : c.sectionMap x ∈ S := by
  induction c with
  | base => exact hx
  | step previous lift _ ih => exact lift.sectionMap_mem ih

theorem CylindricalTower.sectionMap_projection {α : Type} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S)
    (x : α → ℝ) : c.sectionMap x ∘ cadBaseCoordinate n = x := by
  induction c with
  | base => rfl
  | @step n S previous lift h ih =>
    funext a
    exact congrFun ih a

theorem CylindricalTower.sectionMap_continuousOn {α : Type} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S) :
    ContinuousOn c.sectionMap U := by
  induction c with
  | base => exact continuousOn_id
  | step previous lift _ ih =>
    exact lift.sectionMap_continuousOn.comp ih (fun _ hx => previous.sectionMap_mem hx)

theorem CylindricalTower.sectionMap_graph_definable {α : Type} [Finite α]
    {U : Set (α → ℝ)} {n : ℕ} {S : Set (CADVariables α n → ℝ)}
    (c : CylindricalTower U S)
    (hU : (univ : Set ℝ).Definable Language.ring U) :
    (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U c.sectionMap) := by
  letI : Fintype α := Fintype.ofFinite α
  induction c with
  | base => exact coordinateSectionGraph_definable hU id
  | step previous lift _ ih =>
    exact cad_selectedGraph_comp (f := previous.sectionMap) (g := lift.sectionMap) ih
      (lift.sectionMap_graph_definable (previous.region_definable hU))
      (fun _ hx => previous.sectionMap_mem hx)

theorem CylindricalTower.exists_continuous_definable_section {α : Type} [Finite α]
    {U : Set (α → ℝ)} {n : ℕ} {S : Set (CADVariables α n → ℝ)}
    (c : CylindricalTower U S)
    (hU : (univ : Set ℝ).Definable Language.ring U) :
    ∃ f : (α → ℝ) → CADVariables α n → ℝ,
      ContinuousOn f U ∧ MapsTo f U S ∧
      (∀ x, f x ∘ cadBaseCoordinate n = x) ∧
      (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U f) :=
  ⟨c.sectionMap,c.sectionMap_continuousOn,fun _ hx => c.sectionMap_mem hx,
    c.sectionMap_projection,c.sectionMap_graph_definable hU⟩

end PaperI
