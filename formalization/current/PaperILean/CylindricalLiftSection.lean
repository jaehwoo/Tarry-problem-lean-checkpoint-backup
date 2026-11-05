import PaperILean.CylindricalSectionAlgebra

/-! One cylindrical graph or open band over an actual base set. The five
section formulas are proved to be continuous and definable. No nonempty-base,
bounded-cell, positive-dimension, or off-domain continuity premise is used. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

structure CylindricalBoundary {α : Type} (S : Set (α → ℝ)) where
  value : (α → ℝ) → ℝ
  continuousOn : ContinuousOn value S
  graph_definable : (univ : Set ℝ).Definable Language.ring
    (selectedFunctionGraph S (fun x (_ : Unit) => value x))

inductive CylindricalLift {α : Type} (S : Set (α → ℝ)) where
  | graph (f : CylindricalBoundary S)
  | between (lower upper : CylindricalBoundary S)
      (ordered : ∀ x ∈ S, lower.value x < upper.value x)
  | above (lower : CylindricalBoundary S)
  | below (upper : CylindricalBoundary S)
  | whole

def CylindricalLift.region {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) : Set ((α ⊕ Unit) → ℝ) :=
  {v | v ∘ Sum.inl ∈ S ∧ match c with
    | .graph f => v (Sum.inr ()) = f.value (v ∘ Sum.inl)
    | .between l u _ => l.value (v ∘ Sum.inl) < v (Sum.inr ()) ∧
        v (Sum.inr ()) < u.value (v ∘ Sum.inl)
    | .above l => l.value (v ∘ Sum.inl) < v (Sum.inr ())
    | .below u => v (Sum.inr ()) < u.value (v ∘ Sum.inl)
    | .whole => True}

def CylindricalLift.sample {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) (x : α → ℝ) : ℝ :=
  match c with
  | .graph f => f.value x
  | .between l u _ => (l.value x + u.value x) / 2
  | .above l => l.value x + 1
  | .below u => u.value x - 1
  | .whole => 0

def CylindricalLift.sectionMap {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) (x : α → ℝ) : (α ⊕ Unit) → ℝ :=
  Sum.elim x (fun _ => c.sample x)

theorem CylindricalLift.sectionMap_projection {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) (x : α → ℝ) : c.sectionMap x ∘ Sum.inl = x := rfl

theorem CylindricalLift.sectionMap_mem {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) {x : α → ℝ} (hx : x ∈ S) :
    c.sectionMap x ∈ c.region := by
  cases c with
  | graph f => exact ⟨hx,rfl⟩
  | between l u h =>
    change x ∈ S ∧ l.value x < (l.value x + u.value x)/2 ∧
      (l.value x + u.value x)/2 < u.value x
    exact ⟨hx,by linarith [h x hx],by linarith [h x hx]⟩
  | above l => exact ⟨hx,by change l.value x < l.value x + 1; linarith⟩
  | below u => exact ⟨hx,by change u.value x - 1 < u.value x; linarith⟩
  | whole => exact ⟨hx,trivial⟩

theorem CylindricalLift.sample_continuousOn {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) : ContinuousOn c.sample S := by
  cases c with
  | graph f => exact f.continuousOn
  | between l u _ => exact (l.continuousOn.add u.continuousOn).div_const 2
  | above l => exact l.continuousOn.add continuousOn_const
  | below u => exact u.continuousOn.sub continuousOn_const
  | whole => exact continuousOn_const

theorem CylindricalLift.sectionMap_continuousOn {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) : ContinuousOn c.sectionMap S := by
  apply continuousOn_pi.mpr
  intro i
  cases i with
  | inl a => exact (continuous_apply a).continuousOn
  | inr u => exact c.sample_continuousOn

theorem CylindricalLift.sample_graph_definable {α : Type} [Finite α]
    {S : Set (α → ℝ)} (c : CylindricalLift S)
    (hS : (univ : Set ℝ).Definable Language.ring S) :
    (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph S (fun x (_ : Unit) => c.sample x)) := by
  cases c with
  | graph f => exact f.graph_definable
  | between l u h =>
    have heq : (fun x (_ : Unit) => (l.value x + u.value x)/2) =
        (fun x (_ : Unit) => (1/2 : ℝ)*l.value x + (1/2 : ℝ)*u.value x + 0) := by
      funext x t
      ring
    change (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph S (fun x (_ : Unit) => (l.value x + u.value x)/2))
    rw [heq]
    exact cad_selectedGraph_affineCombination l.graph_definable u.graph_definable _ _ _
  | above l =>
    simpa only [one_mul, zero_mul, add_zero] using
      cad_selectedGraph_affineCombination l.graph_definable l.graph_definable 1 0 1
  | below u =>
    simpa only [one_mul, zero_mul, add_zero, sub_eq_add_neg] using
      cad_selectedGraph_affineCombination u.graph_definable u.graph_definable 1 0 (-1)
  | whole => exact cad_selectedGraph_const hS (fun _ : Unit => 0)

theorem CylindricalLift.sectionMap_graph_definable {α : Type} [Finite α]
    {S : Set (α → ℝ)} (c : CylindricalLift S)
    (hS : (univ : Set ℝ).Definable Language.ring S) :
    (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph S c.sectionMap) := by
  letI : Fintype α := Fintype.ofFinite α
  have hid := coordinateSectionGraph_definable hS (id : α → α)
  exact cad_selectedGraph_pair hid (c.sample_graph_definable hS)

theorem CylindricalLift.projection_surjective {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) : (fun v : c.region => ⟨v.val ∘ Sum.inl,v.property.1⟩ : c.region → S).Surjective := by
  intro x
  exact ⟨⟨c.sectionMap x.val,c.sectionMap_mem x.property⟩,Subtype.ext rfl⟩

end PaperI
