import PaperILean.OriginalGaussBodyMatrix
import Mathlib.Analysis.Matrix

/-! I1495--I1499: literal homogeneous diagonal and time normalization.
The general matrix path permits lower shear and diagonal body fields. -/
namespace PaperI.AffineNormalizationMatrices

noncomputable local instance : NormedAddCommGroup (Matrix (Fin 4) (Fin 4) ℝ) :=
  Matrix.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  Matrix.normedSpace

noncomputable def homogeneousDiagonal (sx sy sz : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![sx, sy, sz, 1]

noncomputable def normalizedMatrixPath (G : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (t0 h sx sy sz : ℝ) (s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (homogeneousDiagonal sx sy sz)⁻¹ * (G t0)⁻¹ * G (t0 + h * s) *
    homogeneousDiagonal sx sy sz

noncomputable def normalizedBodyMatrix (sx sy sz h : ℝ)
    (V : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  h • ((homogeneousDiagonal sx sy sz)⁻¹ * V * homogeneousDiagonal sx sy sz)

theorem homogeneousDiagonal_inverse (sx sy sz : ℝ)
    (hx : sx ≠ 0) (hy : sy ≠ 0) (hz : sz ≠ 0) :
    (homogeneousDiagonal sx sy sz)⁻¹ = Matrix.diagonal ![sx⁻¹, sy⁻¹, sz⁻¹, 1] := by
  apply Matrix.inv_eq_left_inv
  rw [homogeneousDiagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hx, hy, hz]

theorem homogeneousDiagonal_isUnit_det (sx sy sz : ℝ)
    (hx : sx ≠ 0) (hy : sy ≠ 0) (hz : sz ≠ 0) :
    IsUnit (homogeneousDiagonal sx sy sz).det := by
  apply isUnit_iff_ne_zero.mpr
  simp [homogeneousDiagonal, Matrix.det_diagonal, Fin.prod_univ_succ, hx, hy, hz]

/-- Entry weights retain the homogeneous coordinate 1 for all translations. -/
theorem normalizedBodyMatrix_apply (sx sy sz h : ℝ)
    (hx : sx ≠ 0) (hy : sy ≠ 0) (hz : sz ≠ 0)
    (V : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    normalizedBodyMatrix sx sy sz h V i j =
      h * V i j * (![sx, sy, sz, 1] : Fin 4 → ℝ) j /
        (![sx, sy, sz, 1] : Fin 4 → ℝ) i := by
  rw [normalizedBodyMatrix, homogeneousDiagonal_inverse sx sy sz hx hy hz]
  simp only [homogeneousDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem fixed_matrix_mul_hasDerivAt
    (G : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (A B W : Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (hg : HasDerivAt G W t) :
    HasDerivAt (fun u => A * G u * B) (A * W * B) t := by
  have hi (i j : Fin 4) : HasDerivAt (fun u => G u i j) (W i j) t :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hg i) j
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simpa only [Matrix.mul_apply] using
    (HasDerivAt.sum (u := Finset.univ) (fun k _ =>
      (HasDerivAt.sum (u := Finset.univ) (fun l _ =>
        (hi l k).const_mul (A i l))).mul_const (B k j)))

theorem normalizedMatrixPath_hasDerivAt
    (G : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Matrix (Fin 4) (Fin 4) ℝ) (t0 h sx sy sz s : ℝ)
    (hg : HasDerivAt G W (t0 + h * s)) :
    HasDerivAt (normalizedMatrixPath G t0 h sx sy sz)
      (h • ((homogeneousDiagonal sx sy sz)⁻¹ * (G t0)⁻¹ * W *
        homogeneousDiagonal sx sy sz)) s := by
  have ht : HasDerivAt (fun u : ℝ => t0 + h * u) h s := by
    simpa using ((hasDerivAt_id s).const_mul h).const_add t0
  have hc : HasDerivAt (fun u => G (t0 + h * u)) (h • W) s :=
    hg.scomp s ht
  have hd := fixed_matrix_mul_hasDerivAt (fun u => G (t0 + h * u))
    ((homogeneousDiagonal sx sy sz)⁻¹ * (G t0)⁻¹)
    (homogeneousDiagonal sx sy sz) (h • W) s hc
  simpa only [normalizedMatrixPath, Matrix.mul_smul, Matrix.smul_mul] using hd

/-- Exact normalization for an actual differentiable invertible matrix path.
The body on the right is the actual inverse-times-derivative at the current point. -/
theorem actual_normalized_matrix_body
    (G : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Matrix (Fin 4) (Fin 4) ℝ) (t0 h sx sy sz s : ℝ)
    (hx : sx ≠ 0) (hy : sy ≠ 0) (hz : sz ≠ 0)
    (hanchor : (G t0).det ≠ 0) (hcurrent : (G (t0 + h * s)).det ≠ 0)
    (hg : HasDerivAt G W (t0 + h * s)) :
    HasDerivAt (normalizedMatrixPath G t0 h sx sy sz)
      (h • ((homogeneousDiagonal sx sy sz)⁻¹ * (G t0)⁻¹ * W *
        homogeneousDiagonal sx sy sz)) s ∧
    (normalizedMatrixPath G t0 h sx sy sz s).det ≠ 0 ∧
    (normalizedMatrixPath G t0 h sx sy sz s)⁻¹ *
      deriv (normalizedMatrixPath G t0 h sx sy sz) s =
      normalizedBodyMatrix sx sy sz h ((G (t0 + h * s))⁻¹ * W) := by
  have hd := normalizedMatrixPath_hasDerivAt G W t0 h sx sy sz s hg
  have hD := homogeneousDiagonal_isUnit_det sx sy sz hx hy hz
  have hG : IsUnit (G (t0 + h * s)).det := isUnit_iff_ne_zero.mpr hcurrent
  have hQ : (normalizedMatrixPath G t0 h sx sy sz s).det ≠ 0 := by
    simp only [normalizedMatrixPath, Matrix.det_mul, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (inv_ne_zero (isUnit_iff_ne_zero.mp hD)) (inv_ne_zero hanchor)) hcurrent)
      (isUnit_iff_ne_zero.mp hD)
  refine ⟨hd, hQ, ?_⟩
  have hderiv : deriv (normalizedMatrixPath G t0 h sx sy sz) s =
      h • ((homogeneousDiagonal sx sy sz)⁻¹ * (G t0)⁻¹ * W *
        homogeneousDiagonal sx sy sz) := hd.deriv
  rw [hderiv]
  have he : h • ((homogeneousDiagonal sx sy sz)⁻¹ * (G t0)⁻¹ * W *
      homogeneousDiagonal sx sy sz) =
      normalizedMatrixPath G t0 h sx sy sz s *
        normalizedBodyMatrix sx sy sz h ((G (t0 + h * s))⁻¹ * W) := by
    simp only [normalizedMatrixPath, normalizedBodyMatrix, Matrix.mul_smul]
    congr 1
    simp only [Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hD,
      Matrix.mul_nonsing_inv_cancel_left _ _ hG]
  rw [he]
  exact Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hQ)

/-- Lower shear and every diagonal rate of the actual normalized path. -/
theorem actual_normalized_lower_and_diagonal_rates
    (G : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Matrix (Fin 4) (Fin 4) ℝ) (t0 h sx sy sz s : ℝ)
    (hx : sx ≠ 0) (hy : sy ≠ 0) (hz : sz ≠ 0)
    (hanchor : (G t0).det ≠ 0) (hcurrent : (G (t0 + h * s)).det ≠ 0)
    (hg : HasDerivAt G W (t0 + h * s)) :
    let V := (G (t0 + h * s))⁻¹ * W
    let Q := normalizedMatrixPath G t0 h sx sy sz
    ((Q s)⁻¹ * deriv Q s) 1 0 = h * V 1 0 * sx / sy ∧
      ∀ i : Fin 4, ((Q s)⁻¹ * deriv Q s) i i = h * V i i := by
  dsimp only
  rw [(actual_normalized_matrix_body G W t0 h sx sy sz s hx hy hz
    hanchor hcurrent hg).2.2]
  constructor
  · simpa using normalizedBodyMatrix_apply sx sy sz h hx hy hz
      ((G (t0 + h * s))⁻¹ * W) 1 0
  · intro i
    rw [normalizedBodyMatrix_apply sx sy sz h hx hy hz]
    fin_cases i <;> simp [hx, hy, hz]

/-- Column-vector convention: the (1,0) generator is zeta*x partial_y. -/
theorem lower_diagonal_generator_action (zeta rx ry rz x y z : ℝ) :
    (!![rx, 0, 0, 0; zeta, ry, 0, 0; 0, 0, rz, 0; 0, 0, 0, 0] :
      Matrix (Fin 4) (Fin 4) ℝ).mulVec ![x, y, z, 1] =
      ![rx * x, zeta * x + ry * y, rz * z, 0] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end PaperI.AffineNormalizationMatrices
