import PaperILean.PolynomialSignDefinability
import Mathlib.Topology.Connected.PathConnected

/-! Actual continuous semialgebraic paths on the closed unit interval. Values
outside the interval are immaterial; the graph retains the interval condition.
No compactness of the target set or differentiability at endpoints is imposed.
Pre-strategy tests: evidence/checkpoint_107_path_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set

def unitPathGraph {κ : Type*} (γ : ℝ → κ → ℝ) : Set ((Unit ⊕ κ) → ℝ) :=
  {v | v (Sum.inl ()) ∈ Icc (0 : ℝ) 1 ∧
    (fun k => v (Sum.inr k)) = γ (v (Sum.inl ()))}

structure SemialgebraicUnitPath {κ : Type*} (S : Set (κ → ℝ))
    (a b : κ → ℝ) where
  toFun : ℝ → κ → ℝ
  continuousOn : ContinuousOn toFun (Icc 0 1)
  mapsTo : MapsTo toFun (Icc 0 1) S
  source : toFun 0 = a
  target : toFun 1 = b
  semialgebraic : HasPolynomialSignDescription (unitPathGraph toFun)

theorem SemialgebraicUnitPath.source_mem {κ : Type*} {S : Set (κ → ℝ)}
    {a b : κ → ℝ} (γ : SemialgebraicUnitPath S a b) : a ∈ S := by
  rw [← γ.source]
  exact γ.mapsTo (by simp)

theorem SemialgebraicUnitPath.target_mem {κ : Type*} {S : Set (κ → ℝ)}
    {a b : κ → ℝ} (γ : SemialgebraicUnitPath S a b) : b ∈ S := by
  rw [← γ.target]
  exact γ.mapsTo (by simp)

theorem unitPathGraph_mem_iff {κ : Type*} (γ : ℝ → κ → ℝ)
    (t : ℝ) (x : κ → ℝ) :
    Sum.elim (fun _ => t) x ∈ unitPathGraph γ ↔ t ∈ Icc (0 : ℝ) 1 ∧ x = γ t :=
  Iff.rfl

theorem SemialgebraicUnitPath.comp_continuousOn {κ : Type*}
    {S : Set (κ → ℝ)} {a b : κ → ℝ} (γ : SemialgebraicUnitPath S a b)
    (f : (κ → ℝ) → ℝ) (hf : ContinuousOn f S) :
    ContinuousOn (fun t => f (γ.toFun t)) (Icc 0 1) :=
  hf.comp γ.continuousOn γ.mapsTo

theorem SemialgebraicUnitPath.comp_range_bound {κ : Type*}
    {S : Set (κ → ℝ)} {a b : κ → ℝ} (γ : SemialgebraicUnitPath S a b)
    (f : (κ → ℝ) → ℝ) (B : ℝ)
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ B) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |f (γ.toFun s) - f (γ.toFun t)| ≤ B :=
  fun _ hs _ ht => hf _ (γ.mapsTo hs) _ (γ.mapsTo ht)

end PaperI
