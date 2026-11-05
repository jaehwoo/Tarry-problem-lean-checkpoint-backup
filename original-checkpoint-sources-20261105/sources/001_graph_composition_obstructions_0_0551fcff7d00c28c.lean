import PaperILean.RawFormulaPolynomialPrenex

-- One common intermediate witness is essential.
example : (∃ x : ℝ, x = 0) ∧ (∃ x : ℝ, x = 1) := ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
example : ¬ ∃ x : ℝ, x = 0 ∧ x = 1 := by
  rintro ⟨x, hx, h1⟩
  norm_num [hx] at h1

-- Retain both graph domains: t=0 maps to0, outside the second domain x>0.
example : ¬ ∃ x : ℝ, ((0:ℝ) ∈ Set.Icc 0 1 ∧ x = 0^2) ∧ (0 < x ∧ 0 = x) := by
  rintro ⟨x, ⟨_, hx⟩, hpos, _⟩
  norm_num [hx] at hpos

-- A path may fail injectivity; graph composition still has its exact value.
example (t z : ℝ) : (∃ x : ℝ, x = t^2 ∧ z = x + 1) ↔ z = t^2 + 1 := by
  simp
example : ((-1:ℝ)^2 = (1:ℝ)^2) ∧ (-1:ℝ) ≠ 1 := by norm_num

-- Parameters are shared before any specialization, including endpoint values.
example (a b t z : ℝ) :
    (∃ x : ℝ, x = (1-t)*a+t*b ∧ z = x+a) ↔ z = (1-t)*a+t*b+a := by
  simp

-- No nonempty coordinate-type hypothesis: the empty coordinate assignment exists uniquely.
example (P : Prop) : (∃ _ : Fin 0 → ℝ, P) ↔ P := by simp
example (x y : Fin 0 → ℝ) : x = y := Subsingleton.elim _ _

-- Restricting the original path domain cannot be silently dropped.
example : ¬ ∃ x : ℝ, ((2:ℝ) ∈ Set.Icc 0 1 ∧ x = 2) ∧ (3 = x + 1) := by norm_num
