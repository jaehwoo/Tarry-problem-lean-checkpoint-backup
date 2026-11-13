import PaperILean.MatrixExpLogInverse

/-! I327: skewness and the reverse anisotropic exponential inclusion.
The inverse logarithms are compared after conjugation, in a proved small
injectivity ball. No small ordinary logarithm norm is assumed. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem matrixLogSeries_norm_lt_half
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ‖A-1‖ < 1/3) :
    ‖matrixLogSeries A‖ < 1/2 := by
  have h := matrixLogSeries_norm_le A (by linarith)
  apply h.trans_lt
  apply (div_lt_iff₀ (by linarith : 0 < 1-‖A-1‖)).mpr
  linarith

theorem matrixLogSeries_inverse_eq_neg
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A*B = 1)
    (hA : ‖A-1‖ < 1/3) (hB : ‖B-1‖ < 1/3) :
    matrixLogSeries B = -matrixLogSeries A := by
  apply matrix_exp_injOn_half_ball (matrixLogSeries_norm_lt_half B hB)
    (by simpa only [Set.mem_setOf_eq, norm_neg] using matrixLogSeries_norm_lt_half A hA)
  apply (NormedSpace.isUnit_exp ℝ (matrixLogSeries A)).mul_left_cancel
  rw [matrix_exp_matrixLogSeries A (by linarith),
    matrix_exp_matrixLogSeries B (by linarith), hAB]
  have h := Matrix.exp_add_of_commute ℝ (matrixLogSeries A) (-matrixLogSeries A)
    (Commute.refl _).neg_right
  simpa only [add_neg_cancel, NormedSpace.exp_zero,
    matrix_exp_matrixLogSeries A (by linarith)] using h

theorem frameConjugate_injective (E : PositiveFrame) : Function.Injective (frameConjugate E) := by
  have hi := Matrix.mul_nonsing_inv E.val (isUnit_iff_ne_zero.mpr E.property.ne')
  have hundo (A : Matrix (Fin 3) (Fin 3) ℝ) : E.val*frameConjugate E A*E.val⁻¹ = A := by
    calc
      E.val*frameConjugate E A*E.val⁻¹ = (E.val*E.val⁻¹)*A*(E.val*E.val⁻¹) := by
        simp only [frameConjugate, Matrix.mul_assoc]
      _ = A := by rw [hi]; simp
  intro A B h
  have hh := congrArg (fun M => E.val*M*E.val⁻¹) h
  simpa only [hundo] using hh

theorem rotationNeighborhood_inverse_small_radius (t : ℝ) (ht : t < 1/10) :
    t/(1-t) < 1/6 := by
  apply (div_lt_iff₀ (by linarith : 0 < 1-t)).mpr
  linarith

theorem rotationLogSeries_inverse_ordinary_domain
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10)
    (O : rotationGroup3) (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    ‖rotationMatrix O⁻¹-1‖ < 1 :=
  rotationNeighborhood_ordinary_norm_lt_one e he (t/(1-t))
    (rotationNeighborhood_inverse_small_radius t ht) O⁻¹
    (rotationNeighborhood_inv_mem _ t (by linarith) O hO)

theorem rotationLogSeries_inv_eq_neg
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10)
    (O : rotationGroup3) (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    rotationLogSeries O⁻¹ = -rotationLogSeries O := by
  let E := positiveDiagonalFrame e he
  have hdom := rotationNeighborhood_source_ordinary_domain e he t ht O hO
  have hdomi := rotationLogSeries_inverse_ordinary_domain e he t ht O hO
  have hA : ‖frameConjugate E (rotationMatrix O)-1‖ < 1/3 :=
    ((mem_rotationNeighborhood_iff E t O).mp hO).trans (by linarith)
  have hBi := (mem_rotationNeighborhood_iff E (t/(1-t)) O⁻¹).mp
    (rotationNeighborhood_inv_mem E t (by linarith) O hO)
  have hB : ‖frameConjugate E (rotationMatrix O⁻¹)-1‖ < 1/3 :=
    hBi.trans ((rotationNeighborhood_inverse_small_radius t ht).trans (by norm_num))
  have hAB : frameConjugate E (rotationMatrix O)*frameConjugate E (rotationMatrix O⁻¹) = 1 := by
    rw [← frameConjugate_mul, ← rotationMatrix_mul, mul_inv_cancel, rotationMatrix_one,
      frameConjugate_one]
  apply frameConjugate_injective E
  change frameConjugate E (matrixLogSeries (rotationMatrix O⁻¹)) =
    frameConjugate E (-matrixLogSeries (rotationMatrix O))
  rw [frameConjugate_matrixLogSeries E _ hdomi]
  change matrixLogSeries (frameConjugate E (rotationMatrix O⁻¹)) =
    frameConjugateCLM E (-matrixLogSeries (rotationMatrix O))
  rw [map_neg, frameConjugateCLM_apply, frameConjugate_matrixLogSeries E _ hdom]
  exact matrixLogSeries_inverse_eq_neg _ _ hAB hA hB

theorem rotationLogSeries_skew
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10)
    (O : rotationGroup3) (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    (rotationLogSeries O)ᵀ = -rotationLogSeries O :=
  (rotationLogSeries_inv_eq_transpose e he t ht O hO).symm.trans
    (rotationLogSeries_inv_eq_neg e he t ht O hO)

theorem matrix_exp_rotationLogSeries
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10)
    (O : rotationGroup3) (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    NormedSpace.exp ℝ (rotationLogSeries O) = rotationMatrix O :=
  matrix_exp_matrixLogSeries _ (rotationNeighborhood_source_ordinary_domain e he t ht O hO)

theorem rotationLogSeries_mem_anisotropicSkewBall
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10)
    (O : rotationGroup3) (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    rotationLogSeries O ∈ anisotropicSkewBall e ((10/9)*t) :=
  ⟨rotationLogSeries_skew e he t ht O hO,
    rotationLogSeries_conjugate_norm_lt_ten_ninths e he t ht O hO⟩

theorem rotationNeighborhood_subset_exp_anisotropicSkewBall
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10) :
    ∀ O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t,
      ∃ H ∈ anisotropicSkewBall e ((10/9)*t), NormedSpace.exp ℝ H = rotationMatrix O := by
  intro O hO
  exact ⟨rotationLogSeries O, rotationLogSeries_mem_anisotropicSkewBall e he t ht O hO,
    matrix_exp_rotationLogSeries e he t ht O hO⟩

theorem rotationLogSeries_source_norm_lt_half
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10)
    (O : rotationGroup3) (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    ‖rotationLogSeries O‖ < 1/2 :=
  anisotropicSkewBall_source_fixed_radius e he t ht _
    (rotationLogSeries_mem_anisotropicSkewBall e he t ht O hO)

theorem rotationMatrix_injective : Function.Injective rotationMatrix := by
  intro O P h
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem rotationLogSeries_injOn_neighborhood
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10) :
    Set.InjOn rotationLogSeries (rotationNeighborhood (positiveDiagonalFrame e he) t) := by
  intro O hO P hP h
  apply rotationMatrix_injective
  rw [← matrix_exp_rotationLogSeries e he t ht O hO,
    ← matrix_exp_rotationLogSeries e he t ht P hP, h]

theorem skewRotationExp_rotationLogSeries
    (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (t : ℝ) (ht : t < 1/10)
    (O : rotationGroup3) (hO : O ∈ rotationNeighborhood (positiveDiagonalFrame e he) t) :
    skewRotationExp (rotationLogSeries O) (rotationLogSeries_skew e he t ht O hO) = O := by
  apply rotationMatrix_injective
  exact matrix_exp_rotationLogSeries e he t ht O hO

end PaperI
