import PaperILean.RegularCoefficientFiberBounds
import PaperILean.RealPolynomialDefinability
noncomputable section
open PaperI

-- The coordinate injection keeps all external and input coordinates, and
-- excludes the new output coordinates; arbitrary polynomial coefficients survive.
example {ι κ : Type} (q : MvPolynomial (ι ⊕ κ) ℝ)
    (p : ι → ℝ) (y x : κ → ℝ) :
    MvPolynomial.eval (Sum.elim (Sum.elim p y) x)
      (MvPolynomial.rename (Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr) q) =
      MvPolynomial.eval (Sum.elim p x) q := by
  rw [MvPolynomial.eval_rename]
  have he : Sum.elim (Sum.elim p y) x ∘ Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr =
      Sum.elim p x := by
    funext a
    cases a <;> rfl
  rw [he]

example {ι κ : Type} (T : (ι → ℝ) → (κ → ℝ) → (κ → ℝ)) :
    regularCoefficientGraph (fun _ => ∅) T = ∅ := by
  ext v
  simp [regularCoefficientGraph]

-- Zero-dimensional output still means equality of the unique empty tuple,
-- so a zero-equation intersection is the full graph domain, not empty.
example : Subsingleton (Fin 0 → ℝ) := inferInstance
example (x y : Fin 0 → ℝ) : x = y := Subsingleton.elim _ _

-- Polynomial degree drops and complete cancellation remain literal equality.
example {ι κ : Type} (q : MvPolynomial (ι ⊕ κ) ℝ) (p : ι → ℝ) (x : κ → ℝ) :
    MvPolynomial.eval (Sum.elim p x) (q-q) = 0 := by simp
