import Revision.Projection

open Set Filter MeasureTheory
open scoped Topology
noncomputable section

namespace PaperI.CollarRevision

open BoundedCharacteristic CorridorBands ShortProjectionCaps ParabolicCollar

/-- The local Jacobian estimate belongs to the same flow as the cap's projection.
The auxiliary extension to time 2m agrees by ODE uniqueness at every used time. -/
theorem cap_projection_derivative {P m τ M δ Λ : ℝ} {C Cf K k H so do' n : ℕ}
    {ι : Type} [DecidableEq ι] {E A Ω : Set Plane} {d v : Plane → ℝ} {keep : Plane → Prop}
    {F : Plane → ℝ → ℝ} {labels : Finset ι} {rep : ι → Plane} {frame : Plane → Fin 6 → ℝ}
    (cap : PhaseCap P m τ Λ K k Cf H so do' n E Ω d v keep F labels rep)
    (hP : 2≤P) (hm : 1≤m) (hτ : 0<τ) (hτm : τ≤m) (hM : 4*m<M)
    (hδ : 0≤δ) (hs : P^C*δ*(2*m)≤Real.log 2)
    (hd : ∀ p∈E,ContDiffAt ℝ 1 d p) (box : ∀ p∈A,CertifiedBox P δ M C Cf E d v frame p)
    (hSub : Ω⊆A) :
    ∀ p∈Ω, ∃ J : ℝ, 1/2≤J ∧ J≤2 ∧ HasFDerivWithinAt (project Ω F) (J • horizontalForm d p) Ω p := by
  classical
  let core := CoreBoxes.of_boxes box
  have hExt (q : Plane) (hq : q∈Ω) :
      ∃ y : ℝ → ℝ, y 0=q.1 ∧ DirectedSolution core.carrier d q.2 1 (-(2*m)) (2*m) y := by
    let B := box q (hSub hq)
    obtain ⟨y,hy,hsol,_⟩ := B.signed_trajectory hP hm hδ hs B.mem_carrier hM B.buffer
    exact ⟨y,hy,solution_mono (core.box_subset (hSub hq)) hsol⟩
  let G (q : Plane) := if h : q∈Ω then Classical.choose (hExt q h) else F q
  have hG (q : Plane) (hq : q∈Ω) :
      G q 0=q.1 ∧ DirectedSolution core.carrier d q.2 1 (-(2*m)) (2*m) (G q) := by
    dsimp only [G]
    rw [dif_pos hq]
    exact Classical.choose_spec (hExt q hq)
  have hWin : window τ⊆window (2*m) := fun t ht => abs_le.mp ((abs_le.mpr ht).trans (by linarith))
  have hEq (q : Plane) (hq : q∈Ω) : project Ω F q=G q (midheight Ω-q.2) := by
    obtain ⟨hTime,hInit,hsol⟩ := cap.time q hq
    have hShort : DirectedSolution E d q.2 1 (-τ) τ (G q) := fun t ht =>
      ⟨core.carrier_subset ((hG q hq).2 t (hWin ht)).1,((hG q hq).2 t (hWin ht)).2.mono hWin⟩
    exact signed_solution_unique hτ.le hd hsol hShort (hInit.trans (hG q hq).1.symm)
      (abs_le.mp (hTime.le.trans (by linarith)))
  intro p hp
  obtain ⟨J,h₁,h₂,hJ⟩ := projection_derivative hP hm hδ core.isOpen_carrier
    (fun q hq => (core.all_rates q hq).1) (fun q hq => (core.all_rates q hq).2.1)
    (fun q hq => (core.all_rates q hq).2.2.1) (fun q hq => (core.all_rates q hq).2.2.2.1)
    (fun q hq => (core.all_rates q hq).2.2.2.2.2.1) (fun q hq => (core.all_rates q hq).2.2.2.2.2.2)
    hs hG (fun q hq => (cap.time q hq).1.le.trans (by linarith)) p hp
  exact ⟨J,h₁,h₂,hJ.congr hEq (hEq p hp)⟩

end PaperI.CollarRevision
