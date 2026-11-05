import PaperILean.OriginalGaussFrozenBodyBounds

/-! I702-I717/I1305: the quadratic reference graph, including its affine terms
and selected profile root. The actual Gauss derivatives and global inverse are
computed; no determinant sign or absolute-coordinate bound is assumed. -/
noncomputable section
namespace PaperI
open scoped ContDiff

def originalQuadraticGraph (r b v t w η : ℝ) (a : Fin 2 → ℝ) : ℝ :=
  η + r/2*(a 0)^2 + b*a 0*a 1 + v/2*(a 1)^2 + t*a 0 + w*a 1

def originalQuadraticGaussInverse (r b t : ℝ) (a : Fin 2 → ℝ) : ℝ :=
  (a 0-b*a 1-t)/r

def originalQuadraticSchur (r b v : ℝ) : ℝ := v-b^2/r

theorem originalQuadraticGraph_contDiff (r b v t w η : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (originalQuadraticGraph r b v t w η) := by
  unfold originalQuadraticGraph
  fun_prop

theorem originalQuadraticGaussInverse_contDiff (r b t : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (originalQuadraticGaussInverse r b t) := by
  unfold originalQuadraticGaussInverse
  simp only [div_eq_mul_inv]
  fun_prop

theorem originalQuadraticGraph_fderiv (r b v t w η : ℝ) (a u : Fin 2 → ℝ) :
    fderiv ℝ (originalQuadraticGraph r b v t w η) a u =
      (r*a 0+b*a 1+t)*u 0 + (b*a 0+v*a 1+w)*u 1 := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) a
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) a
  have h := (((((hasFDerivAt_const η a).add ((h0.mul h0).const_mul (r/2))).add
    ((h0.const_mul b).mul h1)).add ((h1.mul h1).const_mul (v/2))).add
    (h0.const_mul t)).add (h1.const_mul w)
  change fderiv ℝ (fun a : Fin 2 → ℝ =>
    η+r/2*(a 0)^2+b*a 0*a 1+v/2*(a 1)^2+t*a 0+w*a 1) a u = _
  simp only [pow_two]
  rw [h.fderiv]
  simp
  ring

theorem originalQuadraticGraph_Cy (r b v t w η : ℝ) (a : Fin 2 → ℝ) :
    originalGaussCy (originalQuadraticGraph r b v t w η) a = r*a 0+b*a 1+t := by
  simp [originalGaussCy,originalQuadraticGraph_fderiv]

theorem originalQuadraticGraph_Cz (r b v t w η : ℝ) (a : Fin 2 → ℝ) :
    originalGaussCz (originalQuadraticGraph r b v t w η) a = b*a 0+v*a 1+w := by
  simp [originalGaussCz,originalQuadraticGraph_fderiv]

theorem originalQuadraticGraph_R (r b v t w η : ℝ) (a : Fin 2 → ℝ) :
    originalGaussR (originalQuadraticGraph r b v t w η) a = r := by
  unfold originalGaussR
  rw [show originalGaussCy (originalQuadraticGraph r b v t w η) =
    (fun a => r*a 0+b*a 1+t) from funext (originalQuadraticGraph_Cy r b v t w η)]
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) a).const_mul r).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) a).const_mul b)).add_const t
  rw [h.fderiv]
  simp

theorem originalQuadraticGraph_S (r b v t w η : ℝ) (a : Fin 2 → ℝ) :
    originalGaussS (originalQuadraticGraph r b v t w η) a = b := by
  unfold originalGaussS
  rw [show originalGaussCy (originalQuadraticGraph r b v t w η) =
    (fun a => r*a 0+b*a 1+t) from funext (originalQuadraticGraph_Cy r b v t w η)]
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) a).const_mul r).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) a).const_mul b)).add_const t
  rw [h.fderiv]
  simp

theorem originalQuadraticGraph_T (r b v t w η : ℝ) (a : Fin 2 → ℝ) :
    originalGaussT (originalQuadraticGraph r b v t w η) a = v := by
  unfold originalGaussT
  rw [show originalGaussCz (originalQuadraticGraph r b v t w η) =
    (fun a => b*a 0+v*a 1+w) from funext (originalQuadraticGraph_Cz r b v t w η)]
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) a).const_mul b).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) a).const_mul v)).add_const w
  rw [h.fderiv]
  simp

theorem originalQuadraticGraph_shear (r b v t w η : ℝ) (a : Fin 2 → ℝ) :
    originalGaussShear (originalQuadraticGraph r b v t w η) a = -b/r := by
  simp [originalGaussShear,originalQuadraticGraph_R,originalQuadraticGraph_S]

theorem originalQuadraticGraph_determinant (r b v t w η : ℝ) (a : Fin 2 → ℝ) :
    (originalGaussGraphHessian (originalQuadraticGraph r b v t w η) a).det = r*v-b^2 := by
  rw [originalGaussGraphHessian_det _ _
    (originalQuadraticGraph_contDiff r b v t w η 2).contDiffAt]
  rw [originalQuadraticGraph_R,originalQuadraticGraph_S,originalQuadraticGraph_T]

theorem originalQuadraticGaussInverse_right (r b v t w η : ℝ) (hr : r ≠ 0)
    (a : Fin 2 → ℝ) :
    originalGaussCy (originalQuadraticGraph r b v t w η)
      ![originalQuadraticGaussInverse r b t a,a 1] = a 0 := by
  rw [originalQuadraticGraph_Cy]
  simp [originalQuadraticGaussInverse]
  field_simp
  ring

theorem originalQuadraticGaussInverse_left (r b v t w η : ℝ) (hr : r ≠ 0)
    (a : Fin 2 → ℝ) :
    originalQuadraticGaussInverse r b t
      ![originalGaussCy (originalQuadraticGraph r b v t w η) a,a 1] = a 0 := by
  rw [originalQuadraticGraph_Cy]
  simp [originalQuadraticGaussInverse]
  field_simp
  ring

theorem originalQuadraticGaussInverse_unique (r b v t w η : ℝ) (hr : r ≠ 0)
    (a : Fin 2 → ℝ) (y : ℝ) :
    originalGaussCy (originalQuadraticGraph r b v t w η) ![y,a 1] = a 0 ↔
      y = originalQuadraticGaussInverse r b t a := by
  rw [originalQuadraticGraph_Cy]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
  unfold originalQuadraticGaussInverse
  constructor
  · intro h
    apply (eq_div_iff hr).mpr
    nlinarith [h]
  · intro h
    rw [h]
    field_simp
    ring

theorem originalQuadraticGraph_forces_quadratic (r γ : ℝ)
    (hr : r ≠ 0) (hclassification : r*γ = 0) : γ = 0 :=
  (mul_eq_zero.mp hclassification).resolve_left hr

end PaperI
