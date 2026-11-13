import PaperILean.SemialgebraicPathData

/-! Actual half-open semialgebraic curve germs. No existence theorem, analytic
endpoint extension, injectivity, or uniform graph-format bound is hidden here.
The source can belong to C; constant germs and zero dimensions are allowed. -/

noncomputable section
namespace PaperI
open Set

def halfOpenPathGraph {α : Type*} (ε : ℝ) (γ : ℝ → α → ℝ) :
    Set ((Unit ⊕ α) → ℝ) :=
  {v | v (Sum.inl ()) ∈ Ico (0 : ℝ) ε ∧
    (fun i => v (Sum.inr i)) = γ (v (Sum.inl ()))}

structure SemialgebraicCurveGerm {α : Type*} (C : Set (α → ℝ)) (a : α → ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  toFun : ℝ → α → ℝ
  continuousOn : ContinuousOn toFun (Ico 0 radius)
  source : toFun 0 = a
  enters : MapsTo toFun (Ioo 0 radius) C
  semialgebraic : HasPolynomialSignDescription (halfOpenPathGraph radius toFun)

theorem halfOpenPathGraph_mem_iff {α : Type*} (ε : ℝ) (γ : ℝ → α → ℝ)
    (t : ℝ) (x : α → ℝ) :
    Sum.elim (fun _ => t) x ∈ halfOpenPathGraph ε γ ↔
      t ∈ Ico (0 : ℝ) ε ∧ x = γ t := Iff.rfl

theorem SemialgebraicCurveGerm.point_mem {α : Type*}
    {C : Set (α → ℝ)} {a : α → ℝ} (g : SemialgebraicCurveGerm C a)
    {δ : ℝ} (hδ : 0 < δ) (hδε : δ < g.radius) : g.toFun δ ∈ C :=
  g.enters ⟨hδ,hδε⟩

theorem SemialgebraicCurveGerm.nonempty {α : Type*}
    {C : Set (α → ℝ)} {a : α → ℝ} (g : SemialgebraicCurveGerm C a) : C.Nonempty := by
  exact ⟨g.toFun (g.radius / 2), g.point_mem (by linarith [g.radius_pos])
    (by linarith [g.radius_pos])⟩

end PaperI
