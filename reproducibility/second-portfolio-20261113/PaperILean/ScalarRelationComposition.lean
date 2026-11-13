import PaperILean.SemialgebraicPathData
import PaperILean.PublishedHardtTriviality

/-! Exact scalar composition, with one shared intermediate point. Partial
domains are retained; no injectivity of the path is required. Pre-strategy
tests are in `evidence/checkpoint_108_path_pre_strategy.json`. -/

noncomputable section
namespace PaperI
open FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def scalarRelationComposition {κ : Type*}
    (Γ : Set ((Unit ⊕ κ) → ℝ)) (F : Set ((κ ⊕ Unit) → ℝ)) : Set (Fin 2 → ℝ) :=
  {v | ∃ x : κ → ℝ,
    Sum.elim (fun _ => v 0) x ∈ Γ ∧ Sum.elim x (fun _ => v 1) ∈ F}

theorem scalarRelationComposition_mem {κ : Type*}
    (Γ : Set ((Unit ⊕ κ) → ℝ)) (F : Set ((κ ⊕ Unit) → ℝ)) (t y : ℝ) :
    ![t, y] ∈ scalarRelationComposition Γ F ↔
      ∃ x : κ → ℝ, Sum.elim (fun _ => t) x ∈ Γ ∧ Sum.elim x (fun _ => y) ∈ F :=
  Iff.rfl

def scalarRelationCompositionFamily {ρ κ : Type*}
    (Γ : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ))
    (F : Set ((ρ ⊕ (κ ⊕ Unit)) → ℝ)) : Set ((ρ ⊕ Fin 2) → ℝ) :=
  {v | ∃ x : κ → ℝ,
    Sum.elim (fun r => v (Sum.inl r))
      (Sum.elim (fun _ => v (Sum.inr 0)) x) ∈ Γ ∧
    Sum.elim (fun r => v (Sum.inl r))
      (Sum.elim x (fun _ => v (Sum.inr 1))) ∈ F}

theorem scalarRelationCompositionFamily_definable {ρ κ : Type*} [Finite ρ] [Finite κ]
    {Γ : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ)}
    {F : Set ((ρ ⊕ (κ ⊕ Unit)) → ℝ)}
    (hΓ : (Set.univ : Set ℝ).Definable Language.ring Γ)
    (hF : (Set.univ : Set ℝ).Definable Language.ring F) :
    (Set.univ : Set ℝ).Definable Language.ring (scalarRelationCompositionFamily Γ F) := by
  let eΓ : ρ ⊕ (Unit ⊕ κ) → (ρ ⊕ Fin 2) ⊕ κ :=
    Sum.elim (fun r => Sum.inl (Sum.inl r))
      (Sum.elim (fun _ => Sum.inl (Sum.inr 0)) Sum.inr)
  let eF : ρ ⊕ (κ ⊕ Unit) → (ρ ⊕ Fin 2) ⊕ κ :=
    Sum.elim (fun r => Sum.inl (Sum.inl r))
      (Sum.elim Sum.inr (fun _ => Sum.inl (Sum.inr 1)))
  have h := realDefinable_exists ((hΓ.preimage_comp eΓ).inter (hF.preimage_comp eF))
  convert h using 1
  ext v
  apply exists_congr
  intro x
  have heΓ : Sum.elim v x ∘ eΓ = Sum.elim (fun r => v (Sum.inl r))
      (Sum.elim (fun _ => v (Sum.inr 0)) x) := by
    funext a
    rcases a with r | u | k <;> rfl
  have heF : Sum.elim v x ∘ eF = Sum.elim (fun r => v (Sum.inl r))
      (Sum.elim x (fun _ => v (Sum.inr 1))) := by
    funext a
    rcases a with r | k | u <;> rfl
  simp only [Set.mem_inter_iff, Set.mem_preimage, heΓ, heF]

theorem scalarRelationCompositionFamily_fiber {ρ κ : Type*}
    (Γ : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ))
    (F : Set ((ρ ⊕ (κ ⊕ Unit)) → ℝ)) (p : ρ → ℝ) :
    projectionFiber (scalarRelationCompositionFamily Γ F) p =
      scalarRelationComposition (projectionFiber Γ p) (projectionFiber F p) := rfl

def scalarFunctionGraph {κ : Type*} (S : Set (κ → ℝ)) (f : (κ → ℝ) → ℝ) :
    Set ((κ ⊕ Unit) → ℝ) :=
  {v | (fun k => v (Sum.inl k)) ∈ S ∧ v (Sum.inr ()) = f (fun k => v (Sum.inl k))}

theorem scalarFunctionGraph_mem {κ : Type*} (S : Set (κ → ℝ))
    (f : (κ → ℝ) → ℝ) (x : κ → ℝ) (y : ℝ) :
    Sum.elim x (fun _ => y) ∈ scalarFunctionGraph S f ↔ x ∈ S ∧ y = f x := Iff.rfl

/-- On the actual closed parameter interval the partial composition is exactly
the graph of f along the one supplied path. -/
theorem scalarRelationComposition_path_graph {κ : Type*} {S : Set (κ → ℝ)}
    {a b : κ → ℝ} (γ : SemialgebraicUnitPath S a b)
    (F : Set ((κ ⊕ Unit) → ℝ)) (f : (κ → ℝ) → ℝ)
    (hF : ∀ x y, Sum.elim x (fun _ => y) ∈ F ↔ x ∈ S ∧ y = f x)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (y : ℝ) :
    ![t, y] ∈ scalarRelationComposition (unitPathGraph γ.toFun) F ↔ y = f (γ.toFun t) := by
  rw [scalarRelationComposition_mem]
  simp only [unitPathGraph_mem_iff, hF]
  constructor
  · rintro ⟨x, ⟨_, rfl⟩, _, hy⟩
    exact hy
  · intro hy
    exact ⟨γ.toFun t, ⟨ht, rfl⟩, γ.mapsTo ht, hy⟩

theorem scalarRelationComposition_unitPathGraph {κ : Type*} {S : Set (κ → ℝ)}
    {a b : κ → ℝ} (γ : SemialgebraicUnitPath S a b)
    (f : (κ → ℝ) → ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (y : ℝ) :
    ![t, y] ∈ scalarRelationComposition (unitPathGraph γ.toFun) (scalarFunctionGraph S f) ↔
      y = f (γ.toFun t) :=
  scalarRelationComposition_path_graph γ (scalarFunctionGraph S f) f
    (scalarFunctionGraph_mem S f) t ht y

end PaperI
