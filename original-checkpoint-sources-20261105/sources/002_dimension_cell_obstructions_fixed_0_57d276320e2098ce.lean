import PaperILean.FiniteConnectedCover
import PaperILean.PolynomialSignDefinability
import Mathlib.Tactic.NormNum

-- Intrinsic source convention: the empty maximum must not be defaulted to zero.
example : (-1 : ℤ) ≠ 0 := by norm_num

-- The zero-dimensional open cube is nonempty and has exactly one point.
example : Subsingleton {x : Fin 0 → ℝ // ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1} := inferInstance
example (n : ℕ) : Nonempty {x : Fin n → ℝ // ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1} :=
  ⟨⟨fun _ => 1 / 2, by intro i; norm_num⟩⟩

-- A positive-dimensional cube has distinct points; it cannot be a point cell.
example : ∃ x y : {x : Fin 1 → ℝ // ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1}, x ≠ y := by
  let x : {x : Fin 1 → ℝ // ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1} :=
    ⟨fun _ => 1 / 4, by intro i; norm_num⟩
  let y : {x : Fin 1 → ℝ // ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1} :=
    ⟨fun _ => 3 / 4, by intro i; norm_num⟩
  refine ⟨x, y, ?_⟩
  intro h
  have he := congrArg (fun z => z.val 0) h
  norm_num [x, y] at he

-- No nonempty cube can map into an empty target, even without injectivity.
example (n : ℕ) : ¬ Nonempty ({x : Fin n → ℝ //
    ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1} → Empty) := by
  rintro ⟨f⟩
  exact (f ⟨fun _ => 1 / 2, by intro i; norm_num⟩).elim
