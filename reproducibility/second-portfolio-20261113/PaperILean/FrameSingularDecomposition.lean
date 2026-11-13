import PaperILean.FrameSingularValues
import PaperILean.OrientedSpectralBasis
import PaperILean.RotationOrientationFrames

/-! I311-315,331: the singular-value-to-Gram bridge.
The input singular values are defined from B^T B, with multiplicity, independently
of the decomposition concluded here. Both orthogonal factors have determinant one.
Repeated positive lengths are allowed; no spectral gap is used. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

theorem positiveFrame_rotation_of_rightGram (E C : PositiveFrame)
    (h : E.valᵀ * E.val = C.valᵀ * C.val) :
    ∃ O : rotationGroup3, C.val = rotationMatrix O * E.val := by
  let Et : PositiveFrame := ⟨E.valᵀ, by simpa only [Matrix.det_transpose] using E.property⟩
  let Ct : PositiveFrame := ⟨C.valᵀ, by simpa only [Matrix.det_transpose] using C.property⟩
  have ht : Et.val * Et.valᵀ = Ct.val * Ct.valᵀ := by
    simpa only [Et, Ct, Matrix.transpose_transpose] using h
  obtain ⟨Q, hQ, hd, hC⟩ := (same_gram_iff_right_specialOrthogonal Et Ct).mp ht
  have hmem : Qᵀ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    refine ⟨?_, ?_⟩
    · apply (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mpr
      simpa only [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using
        (Matrix.mul_eq_one_comm.mp hQ)
    · change (Qᵀ).det = 1
      simpa only [Matrix.det_transpose] using hd
  obtain ⟨O, hO⟩ := (exists_rotationMatrix_iff Qᵀ).mpr hmem
  refine ⟨O, ?_⟩
  rw [hO]
  simpa only [Et, Ct, Matrix.transpose_mul, Matrix.transpose_transpose] using
    congrArg Matrix.transpose hC

theorem frame_singular_oriented_rightGram (B : PositiveFrame) (e : Fin 3 → ℝ)
    (he : HasFrameSingularValues B e) :
    ∃ V : rotationGroup3, (B.val * rotationMatrix V)ᵀ * (B.val * rotationMatrix V) =
      Matrix.diagonal (fun i => (e i)^2) := by
  obtain ⟨σ, hσ⟩ := hasFrameSingularValues_sq B e he
  obtain ⟨V, hV⟩ := exists_oriented_spectral_diagonal (B.valᵀ * B.val)
    (frame_rightGram_posDef B).isHermitian σ
  refine ⟨V, ?_⟩
  calc
    (B.val * rotationMatrix V)ᵀ * (B.val * rotationMatrix V) =
        (rotationMatrix V)ᵀ * (B.valᵀ * B.val) * rotationMatrix V := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Matrix.diagonal ((frame_rightGram_posDef B).isHermitian.eigenvalues ∘ σ) := hV
    _ = Matrix.diagonal (fun i => (e i)^2) := by
      exact congrArg Matrix.diagonal (funext (fun i => (hσ i).symm))

theorem frame_specialOrthogonal_singular_decomposition (B : PositiveFrame)
    (e : Fin 3 → ℝ) (he : HasFrameSingularValues B e) :
    ∃ O V : rotationGroup3,
      B.val = rotationMatrix O * Matrix.diagonal e * (rotationMatrix V)ᵀ := by
  obtain ⟨V, hV⟩ := frame_singular_oriented_rightGram B e he
  let E := positiveDiagonalFrame e (hasFrameSingularValues_pos B e he)
  let C : PositiveFrame := ⟨B.val * rotationMatrix V, by
    rw [Matrix.det_mul, rotationMatrix_det, mul_one]
    exact B.property⟩
  have hgram : E.valᵀ * E.val = C.valᵀ * C.val := by
    change (Matrix.diagonal e)ᵀ * Matrix.diagonal e =
      (B.val * rotationMatrix V)ᵀ * (B.val * rotationMatrix V)
    rw [hV, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    simp only [pow_two]
  obtain ⟨O, hO⟩ := positiveFrame_rotation_of_rightGram E C hgram
  refine ⟨O, V, ?_⟩
  calc
    B.val = B.val * (rotationMatrix V * (rotationMatrix V)ᵀ) := by
      rw [rotationMatrix_orthogonal, Matrix.mul_one]
    _ = (B.val * rotationMatrix V) * (rotationMatrix V)ᵀ := by
      rw [Matrix.mul_assoc]
    _ = rotationMatrix O * Matrix.diagonal e * (rotationMatrix V)ᵀ := by
      exact congrArg (fun X => X * (rotationMatrix V)ᵀ) hO

theorem frame_singular_gram_representation (B : PositiveFrame) (e : Fin 3 → ℝ)
    (hepos : ∀ i, 0 < e i) (he : HasFrameSingularValues B e) :
    ∃ O : rotationGroup3,
      (rotatedPositiveFrame (positiveDiagonalFrame e hepos) O).val *
        (rotatedPositiveFrame (positiveDiagonalFrame e hepos) O).valᵀ =
      B.val * B.valᵀ := by
  obtain ⟨O, V, hB⟩ := frame_specialOrthogonal_singular_decomposition B e he
  refine ⟨O, ?_⟩
  have hVT : (rotationMatrix V)ᵀ * ((rotationMatrix V)ᵀ)ᵀ = 1 := by
    simpa only [Matrix.transpose_transpose] using
      (Matrix.mul_eq_one_comm.mp (rotationMatrix_orthogonal V))
  rw [hB, frameGram_right_orthogonal _ _ hVT]
  rfl

theorem exists_ordered_specialOrthogonal_singular_decomposition (B : PositiveFrame) :
    ∃ e : Fin 3 → ℝ, (∀ i, 0 < e i) ∧ e 0 ≤ e 1 ∧ e 1 ≤ e 2 ∧
      HasFrameSingularValues B e ∧ ∃ O V : rotationGroup3,
        B.val = rotationMatrix O * Matrix.diagonal e * (rotationMatrix V)ᵀ := by
  obtain ⟨e, hp, h01, h12, hs⟩ := exists_ordered_frameSingularValues B
  exact ⟨e, hp, h01, h12, hs, frame_specialOrthogonal_singular_decomposition B e hs⟩

end PaperI
