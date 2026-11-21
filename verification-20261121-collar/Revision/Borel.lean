import Revision.CapInterval
import PaperILean.ShortProjectionCapsWhole

open Set MeasureTheory
noncomputable section
namespace PaperI.CollarRevision
open BoundedCharacteristic ShortProjectionCaps

private abbrev CapTuple := ℝ × ℝ × ℝ × ℝ × ℝ

/-- The last two entries are the original rounded scale tag. -/
private def retag (m : ℝ) (t : CapTuple) : CapTuple :=
  let lo := t.2.1+m/2
  let hi := t.2.2.1-m/2
  let r := (max m (hi-lo)-(hi-lo))/2
  (t.1,lo-r,hi+r,t.2.2.2)

private theorem retag_measurable (m : ℝ) : Measurable (retag m) := by
  unfold retag
  fun_prop

theorem exact_tag (m : ℝ) (Ω : Set Plane) (F : Plane → ℝ → ℝ) :
    let I := project Ω F '' Ω
    retag m (capTag m Ω F) = (midheight Ω,capLeft I m,capRight I m,capLength I m,capWidth m) := by
  simp [retag,capTag,leftEnd,rightEnd,capLeft,capRight,pad,horizontalSpan]

/-- Borel endpoints, heights and scale tags on the input coefficient space of the short family. -/
theorem measurable_exact_short_family {ρ ι : Type} [DecidableEq ι] {P m τ Λ : ℝ}
    {K k Cf H fs fd n : ℕ} {E G : Set ((ρ ⊕ Fin 2) → ℝ)}
    {d v : (ρ → ℝ) → Plane → ℝ} {keep : (ρ → ℝ) → Plane → Prop}
    {labels : projectionDomain G → Finset ι} {rep : projectionDomain G → ι → Plane}
    (A : CorridorCapAssignment P m τ Λ K k Cf H fs fd n E G d v keep labels rep) :
    ∃ F : projectionDomain G → Plane → ℝ → ℝ,
      (∀ p, PhaseCap P m τ Λ K k Cf H fs fd n (planeFiber E p.val) (planeFiber G p.val)
        (d p.val) (v p.val) (keep p.val) (F p) (labels p) (rep p)) ∧
      Measurable (fun p : projectionDomain G =>
        let Ω := planeFiber G p.val
        let I := project Ω (F p) '' Ω
        (midheight Ω,capLeft I m,capRight I m,capLength I m,capWidth m)) := by
  obtain ⟨F,hF,hM,_⟩ := A.common
  use F,hF
  simpa only [Function.comp_def,exact_tag] using (retag_measurable m).comp hM

end PaperI.CollarRevision
