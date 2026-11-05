import PaperILean.AugmentedStoppedTopology
import Mathlib.Algebra.MvPolynomial.CommRing

/-! I595-607, I623-638: polynomial coordinates of the inherited orbit maps.
The coefficients depend only on the fixed degree and row/column indices,
not on the state, P, or a direction. No physical coordinate is removed. -/

noncomputable section
open scoped Matrix BigOperators
namespace PaperI

def linearCoordinatePolynomial {α β : Type*} [Fintype α]
    (f : (α → ℝ) →ₗ[ℝ] (β → ℝ)) (i : β) : MvPolynomial α ℝ := by
  classical
  exact ∑ j, MvPolynomial.C (LinearMap.toMatrix' f i j) * MvPolynomial.X j

theorem eval_linearCoordinatePolynomial {α β : Type*} [Fintype α]
    (f : (α → ℝ) →ₗ[ℝ] (β → ℝ)) (i : β) (v : α → ℝ) :
    MvPolynomial.eval v (linearCoordinatePolynomial f i) = f v i := by
  classical
  simp only [linearCoordinatePolynomial, MvPolynomial.eval_sum,
    map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  change (LinearMap.toMatrix' f *ᵥ v) i = f v i
  exact congrArg (fun g : (α → ℝ) →ₗ[ℝ] (β → ℝ) => g v i)
    (Matrix.toLin'_toMatrix' f)

theorem linearCoordinatePolynomial_degree {α β : Type*} [Fintype α]
    (f : (α → ℝ) →ₗ[ℝ] (β → ℝ)) (i : β) :
    (linearCoordinatePolynomial f i).totalDegree ≤ 1 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

def augmentedOrbitCoordinateStateMap (k : ℕ) (j : Fin 6) :
    (AugmentedCoordinateIndex k → ℝ) →ₗ[ℝ] (AugmentedCoordinateIndex k → ℝ) :=
  (augmentedStateCoordinates k).toLinearMap.comp
    ((augmentedOrbitStateMap k (Pi.single j 1)).comp
      (augmentedStateCoordinates k).symm.toLinearMap)

def augmentedOrbitEntryPolynomial (k : ℕ) (i : AugmentedCoordinateIndex k) (j : Fin 6) :
    MvPolynomial (AugmentedCoordinateIndex k) ℝ :=
  linearCoordinatePolynomial (augmentedOrbitCoordinateStateMap k j) i

theorem eval_augmentedOrbitEntryPolynomial (k : ℕ) (S : AugmentedState k)
    (i : AugmentedCoordinateIndex k) (j : Fin 6) :
    MvPolynomial.eval (augmentedStateCoordinates k S)
      (augmentedOrbitEntryPolynomial k i j) = augmentedOrbitMatrix k S i j := by
  rw [augmentedOrbitEntryPolynomial, eval_linearCoordinatePolynomial,
    augmentedOrbitMatrix_column]
  simp [augmentedOrbitCoordinateStateMap, augmentedOrbitStateMap]

theorem augmentedOrbitEntryPolynomial_degree (k : ℕ)
    (i : AugmentedCoordinateIndex k) (j : Fin 6) :
    (augmentedOrbitEntryPolynomial k i j).totalDegree ≤ 1 :=
  linearCoordinatePolynomial_degree _ _

def normalOrbitEntryPolynomial (k : ℕ) (i : AugmentedCoordinateIndex k) (j : Fin 3) :
    MvPolynomial (AugmentedCoordinateIndex k) ℝ :=
  augmentedOrbitEntryPolynomial k i (j.castLE (by decide))

theorem eval_normalOrbitEntryPolynomial (k : ℕ) (S : AugmentedState k)
    (i : AugmentedCoordinateIndex k) (j : Fin 3) :
    MvPolynomial.eval (augmentedStateCoordinates k S)
      (normalOrbitEntryPolynomial k i j) = normalOrbitMatrix k S i j := by
  rw [normalOrbitEntryPolynomial, eval_augmentedOrbitEntryPolynomial,
    normalOrbitMatrix_first_three]

theorem normalOrbitEntryPolynomial_degree (k : ℕ)
    (i : AugmentedCoordinateIndex k) (j : Fin 3) :
    (normalOrbitEntryPolynomial k i j).totalDegree ≤ 1 :=
  augmentedOrbitEntryPolynomial_degree _ _ _

end PaperI
