import PaperILean.CylindricalSlicedFamilyFormats

/-! Exact packing of parameter and output coordinates. In particular the
recursive output order is preserved, including n=0. No topological change of
fiber closure or parameter domain occurs in this coordinate transport. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def cadUnpackCoordinate {ρ : Type} : (n : ℕ) → CADVariables ρ n → ρ ⊕ Fin n
  | 0 => Sum.inl
  | n+1 => Sum.elim (Sum.map id Fin.succ ∘ cadUnpackCoordinate n) (fun _ => Sum.inr 0)

theorem cadPack_eq_comp {ρ : Type} (n : ℕ) (p : ρ → ℝ) (x : Fin n → ℝ) :
    cadPack n p x = Sum.elim p x ∘ cadUnpackCoordinate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext k
    cases k with
    | inl k =>
      have h := congrFun (ih (fun i => x i.succ)) k
      change cadPack n p (fun i => x i.succ) k = _
      rw [h]
      change Sum.elim p (fun i => x i.succ) (cadUnpackCoordinate n k) =
        Sum.elim p x (Sum.map id Fin.succ (cadUnpackCoordinate n k))
      cases cadUnpackCoordinate n k <;> rfl
    | inr k => rfl

theorem cadPack_reconstruct {ρ : Type} (n : ℕ) (z : CADVariables ρ n → ℝ) :
    cadPack n (z ∘ cadBaseCoordinate n) (z ∘ cadOutputCoordinate n) = z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext k
    cases k with
    | inl k => exact congrFun (ih (z ∘ Sum.inl)) k
    | inr k => cases k; rfl

def cadPackedRelation {ρ : Type} (n : ℕ) (S : Set (CADVariables ρ n → ℝ)) :
    Set ((ρ ⊕ Fin n) → ℝ) :=
  {v | cadPack n (v ∘ Sum.inl) (v ∘ Sum.inr) ∈ S}

theorem cadPackedRelation_definable {ρ : Type} (n : ℕ)
    {S : Set (CADVariables ρ n → ℝ)} (hS : (univ : Set ℝ).Definable Language.ring S) :
    (univ : Set ℝ).Definable Language.ring (cadPackedRelation n S) := by
  convert hS.preimage_comp (cadUnpackCoordinate n) using 1
  ext v
  change cadPack n (v ∘ Sum.inl) (v ∘ Sum.inr) ∈ S ↔ v ∘ cadUnpackCoordinate n ∈ S
  rw [cadPack_eq_comp]
  have he : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
    funext i; cases i <;> rfl
  rw [he]

theorem cadPackedRelation_fiber {ρ : Type} (n : ℕ) (S : Set (CADVariables ρ n → ℝ))
    (p : ρ → ℝ) : projectionFiber (cadPackedRelation n S) p = {x | cadPack n p x ∈ S} := rfl

theorem cadPack_selectedGraph {α ρ : Type} [Finite α] [Finite ρ]
    {D : Set (α → ℝ)} (n : ℕ) {p : (α → ℝ) → ρ → ℝ} {x : (α → ℝ) → Fin n → ℝ}
    (hp : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D p))
    (hx : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D x)) :
    (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph D (fun a => cadPack n (p a) (x a))) := by
  simpa only [cadPack_eq_comp] using
    cad_selectedGraph_coordinates (cad_selectedGraph_pair hp hx) (cadUnpackCoordinate n)

end PaperI
