import PaperILean.CylindricalCADInput
import PaperILean.CylindricalEndpointFormats

/-! Insert and remove one auxiliary base coordinate without changing outputs.
All identities include height zero. No geometric or published input is used.
Prospective screens: evidence/checkpoint_119_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def cadKeepCoordinate {ρ : Type} : (n : ℕ) → CADVariables ρ n → CADVariables (ρ ⊕ Unit) n
  | 0 => Sum.inl
  | n+1 => Sum.map (cadKeepCoordinate n) id

def cadDropTime {ρ : Type} (n : ℕ) (z : CADVariables (ρ ⊕ Unit) n → ℝ) :
    CADVariables ρ n → ℝ := z ∘ cadKeepCoordinate n

def cadInsertTime {ρ : Type} : (n : ℕ) → (CADVariables ρ n → ℝ) → ℝ →
    CADVariables (ρ ⊕ Unit) n → ℝ
  | 0, z, t => Sum.elim z (fun _ => t)
  | n+1, z, t => Sum.elim (cadInsertTime n (z ∘ Sum.inl) t) (z ∘ Sum.inr)

theorem cadDropTime_insert {ρ : Type} (n : ℕ) (z : CADVariables ρ n → ℝ) (t : ℝ) :
    cadDropTime n (cadInsertTime n z t) = z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    cases i with
    | inl i => exact congrFun (ih (z := z ∘ Sum.inl)) i
    | inr i => rfl

theorem cadInsertTime_drop {ρ : Type} (n : ℕ) (z : CADVariables (ρ ⊕ Unit) n → ℝ) :
    cadInsertTime n (cadDropTime n z) (z (cadBaseCoordinate n (Sum.inr ()))) = z := by
  induction n with
  | zero => funext i; cases i with
    | inl i => rfl
    | inr i => cases i; rfl
  | succ n ih =>
    funext i
    cases i with
    | inl i => exact congrFun (ih (z := z ∘ Sum.inl)) i
    | inr i => rfl

theorem cadDropTime_base {ρ : Type} (n : ℕ) (z : CADVariables (ρ ⊕ Unit) n → ℝ) :
    cadDropTime n z ∘ cadBaseCoordinate n = (z ∘ cadBaseCoordinate n) ∘ Sum.inl := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (z := z ∘ Sum.inl)

theorem cadInsertTime_base {ρ : Type} (n : ℕ) (z : CADVariables ρ n → ℝ) (t : ℝ) :
    cadInsertTime n z t ∘ cadBaseCoordinate n =
      Sum.elim (z ∘ cadBaseCoordinate n) (fun _ => t) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (z := z ∘ Sum.inl)

theorem cadDropTime_continuous {ρ : Type} (n : ℕ) : Continuous (@cadDropTime ρ n) :=
  continuous_pi (fun i => continuous_apply (cadKeepCoordinate n i))

theorem cadInsertTime_graph_definable {α ρ : Type} [Finite α] [Finite ρ]
    {D : Set (α → ℝ)} (n : ℕ) {z : (α → ℝ) → CADVariables ρ n → ℝ}
    {t : (α → ℝ) → ℝ}
    (hz : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D z))
    (ht : CADScalarDefinable D t) :
    (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph D (fun p => cadInsertTime n (z p) (t p))) := by
  induction n with
  | zero => exact cad_selectedGraph_pair hz ht
  | succ n ih =>
    exact cad_selectedGraph_pair (ih (cad_selectedGraph_coordinates hz Sum.inl))
      (cad_selectedGraph_coordinates hz Sum.inr)

theorem cad_selectedGraph_preimage {α β : Type} [Finite α] [Finite β]
    {U : Set (α → ℝ)} {V : Set (β → ℝ)} {f : (α → ℝ) → β → ℝ}
    (hf : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U f))
    (hV : (univ : Set ℝ).Definable Language.ring V) :
    (univ : Set ℝ).Definable Language.ring {x | x ∈ U ∧ f x ∈ V} := by
  have h := realDefinable_exists (hf.inter (hV.preimage_comp Sum.inr))
  convert h using 1
  ext x
  change (x ∈ U ∧ f x ∈ V) ↔ ∃ y, (x ∈ U ∧ f x = y) ∧ y ∈ V
  exact ⟨fun h => ⟨f x,⟨h.1,rfl⟩,h.2⟩,fun ⟨y,⟨hx,hy⟩,hv⟩ => ⟨hx,hy.symm ▸ hv⟩⟩

end PaperI
