import PaperILean.RawGraphComposition
namespace PaperI.Checkpoint106
private def coordinateOrder : Unit ⊕ Unit → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)
example (t y : ℝ) : (![t,y] ∘ coordinateOrder) (Sum.inl ()) = t := by rfl
example (t y : ℝ) : (![t,y] ∘ coordinateOrder) (Sum.inr ()) = y := by rfl
example (t y : ℝ) : ![t,y] ∘ coordinateOrder = Sum.elim (fun _ => t) (fun _ => y) := by
  funext i
  cases i <;> rfl
example : (![0,1] ∘ coordinateOrder) (Sum.inl ()) ≠ (![0,1] ∘ coordinateOrder) (Sum.inr ()) := by
  norm_num [coordinateOrder]
end PaperI.Checkpoint106
