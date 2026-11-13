import PaperILean.StoppedOrbitRank

/-! I595-607 and I668-693: the exact matrices and Euclidean coordinate maps
for the full augmented differential and its first three normal columns.
No equivalence with the ambient function or product norm is assumed. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

def normalOrbitMatrix (k : ℕ) (S : AugmentedState k) :
    Matrix (AugmentedCoordinateIndex k) (Fin 3) ℝ :=
  LinearMap.toMatrix' ((augmentedStateCoordinates k).toLinearMap.comp
    (normalOrbitDifferential k S))

theorem normalOrbitMatrix_mulVec {k : ℕ} (S : AugmentedState k) (v : Fin 3 → ℝ) :
    normalOrbitMatrix k S *ᵥ v =
      augmentedStateCoordinates k (normalOrbitDifferential k S v) := by
  exact congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] (AugmentedCoordinateIndex k → ℝ) => f v)
    (Matrix.toLin'_toMatrix' ((augmentedStateCoordinates k).toLinearMap.comp
      (normalOrbitDifferential k S)))

theorem normalOrbitMatrix_column {k : ℕ} (S : AugmentedState k)
    (i : AugmentedCoordinateIndex k) (j : Fin 3) :
    normalOrbitMatrix k S i j =
      augmentedStateCoordinates k (normalOrbitDifferential k S (Pi.single j 1)) i := by
  rw [normalOrbitMatrix, LinearMap.toMatrix'_apply]
  have heq : (fun h : Fin 3 => if h = j then (1 : ℝ) else 0) = Pi.single j 1 := by
    funext h
    simp [Pi.single_apply, eq_comm]
  rw [heq]
  rfl

theorem normalCoordinates_single (j : Fin 3) :
    normalCoordinates (Pi.single j 1) = Pi.single (j.castLE (by decide) : Fin 6) 1 := by
  ext i
  fin_cases j <;> fin_cases i <;> simp [normalCoordinates, Pi.single_apply]

theorem normalOrbitMatrix_first_three {k : ℕ} (S : AugmentedState k)
    (i : AugmentedCoordinateIndex k) (j : Fin 3) :
    normalOrbitMatrix k S i j = augmentedOrbitMatrix k S i (j.castLE (by decide)) := by
  rw [normalOrbitMatrix_column, augmentedOrbitMatrix_column,
    normalOrbitDifferential_apply, normalCoordinates_single]

theorem normalOrbitMatrix_rank_eq {k : ℕ} (S : AugmentedState k) :
    (normalOrbitMatrix k S).rank =
      Module.finrank ℝ (LinearMap.range (normalOrbitDifferential k S)) := by
  have heq : (normalOrbitMatrix k S).mulVecLin =
      (augmentedStateCoordinates k).toLinearMap.comp (normalOrbitDifferential k S) := by
    apply LinearMap.ext
    intro v
    exact normalOrbitMatrix_mulVec S v
  rw [Matrix.rank, heq, LinearMap.range_comp]
  exact (augmentedStateCoordinates k).finrank_map_eq _

theorem stopped_normalOrbitMatrix_rank {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    (normalOrbitMatrix k S).rank = 3 := by
  rw [normalOrbitMatrix_rank_eq, stopped_normalOrbit_finrank hP S hstop]

def augmentedStateEuclideanCoordinates (k : ℕ) :
    AugmentedState k ≃ₗ[ℝ] EuclideanSpace ℝ (AugmentedCoordinateIndex k) :=
  (augmentedStateCoordinates k).trans
    (WithLp.linearEquiv 2 ℝ (AugmentedCoordinateIndex k → ℝ)).symm

theorem augmentedStateEuclideanCoordinates_norm {k : ℕ} (S : AugmentedState k) :
    ‖augmentedStateEuclideanCoordinates k S‖ = augmentedStateNorm S := by
  symm
  exact coordinateL2Norm_eq_norm _

theorem normalCoordinates_norm (v : Fin 3 → ℝ) :
    coordinateL2Norm (normalCoordinates v) = coordinateL2Norm v := by
  simp [coordinateL2Norm, normalCoordinates, Fin.sum_univ_succ]

def augmentedOrbitEuclidean (k : ℕ) (S : AugmentedState k) :
    EuclideanSpace ℝ (Fin 6) →ₗ[ℝ] EuclideanSpace ℝ (AugmentedCoordinateIndex k) :=
  Matrix.toEuclideanLin (augmentedOrbitMatrix k S)

def normalOrbitEuclidean (k : ℕ) (S : AugmentedState k) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (AugmentedCoordinateIndex k) :=
  Matrix.toEuclideanLin (normalOrbitMatrix k S)

theorem augmentedOrbitEuclidean_apply {k : ℕ} (S : AugmentedState k)
    (ξ : EuclideanSpace ℝ (Fin 6)) :
    augmentedOrbitEuclidean k S ξ = augmentedStateEuclideanCoordinates k
      (augmentedOrbitDifferential k S ((WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)) ξ)) := by
  change (WithLp.equiv 2 (AugmentedCoordinateIndex k → ℝ)).symm
    (augmentedOrbitMatrix k S *ᵥ ((WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)) ξ)) = _
  rw [augmentedOrbitMatrix_mulVec]
  rfl

theorem normalOrbitEuclidean_apply {k : ℕ} (S : AugmentedState k)
    (v : EuclideanSpace ℝ (Fin 3)) :
    normalOrbitEuclidean k S v = augmentedStateEuclideanCoordinates k
      (normalOrbitDifferential k S ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)) v)) := by
  change (WithLp.equiv 2 (AugmentedCoordinateIndex k → ℝ)).symm
    (normalOrbitMatrix k S *ᵥ ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)) v)) = _
  rw [normalOrbitMatrix_mulVec]
  rfl

theorem augmentedOrbitEuclidean_norm {k : ℕ} (S : AugmentedState k)
    (ξ : EuclideanSpace ℝ (Fin 6)) :
    ‖augmentedOrbitEuclidean k S ξ‖ = augmentedStateNorm
      (augmentedOrbitDifferential k S ((WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)) ξ)) := by
  rw [augmentedOrbitEuclidean_apply, augmentedStateEuclideanCoordinates_norm]

theorem normalOrbitEuclidean_norm {k : ℕ} (S : AugmentedState k)
    (v : EuclideanSpace ℝ (Fin 3)) :
    ‖normalOrbitEuclidean k S v‖ = augmentedStateNorm
      (normalOrbitDifferential k S ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)) v)) := by
  rw [normalOrbitEuclidean_apply, augmentedStateEuclideanCoordinates_norm]

theorem stopped_normalOrbitEuclidean_injective {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    Function.Injective (normalOrbitEuclidean k S) := by
  intro v w h
  rw [normalOrbitEuclidean_apply, normalOrbitEuclidean_apply] at h
  exact (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).injective
    (stopped_normalOrbit_injective hP S hstop
      ((augmentedStateEuclideanCoordinates k).injective h))

end PaperI
