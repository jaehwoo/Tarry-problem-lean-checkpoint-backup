import PaperILean.NormalFibersJets
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Matrix.Notation
import PaperILean.NormalJacobianDeterminant

/-! Actual ordinary normalization Jacobians for I3263--I3265 and I3276.
The equations are full pullback values, with constants retained. Coordinates
are exactly `(c,a,b,d)`. Every differential below is proved for the actual map. -/

noncomputable section
namespace PaperI.NormalFibers

abbrev FrameSpace := Fin 4 → ℝ

/-- The four literal defining equations of source chart I. -/
def normalizationEquationsI (G : Poly) (e f : ℝ) (w : FrameSpace) : FrameSpace :=
  ![MvPolynomial.eval 0 (pullback w e f G),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (pullback w e f G)),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (pullback w e f G)),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (pullback w e f G)))]

/-- The four literal defining equations of source chart II. -/
def normalizationEquationsII (G : Poly) (e f : ℝ) (w : FrameSpace) : FrameSpace :=
  ![MvPolynomial.eval 0 (pullback w e f G),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (pullback w e f G)),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (pullback w e f G)),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (pullback w e f G)))]

/-- Ordinary Jacobian, in the standard coordinate basis. -/
def ordinaryJacobian (F : FrameSpace → FrameSpace) (w : FrameSpace) :
    Matrix (Fin 4) (Fin 4) ℝ := fun i j => (fderiv ℝ F w (Pi.single j 1)) i

private def coord (i : Fin 4) : FrameSpace →L[ℝ] ℝ := ContinuousLinearMap.proj i

private def fieldD (P : Poly) (e f : ℝ) (w : FrameSpace) : FrameSpace →L[ℝ] ℝ :=
  firstAt P e f 0 (w 0) • coord 0

private theorem hasFDerivAt_field (P : Poly) (e f : ℝ) (w : FrameSpace) :
    HasFDerivAt (fun u : FrameSpace => valueAt P e f (u 0)) (fieldD P e f w) w := by
  have hp : HasDerivAt (fun c => valueAt P e f c) (firstAt P e f 0 (w 0)) (w 0) := by
    simpa only [linePolynomial_eval, linePolynomial_derivative] using
      (linePolynomial P e f).hasDerivAt (w 0)
  exact hp.comp_hasFDerivAt w (hasFDerivAt_apply (𝕜 := ℝ) 0 w)

private def yD (G : Poly) (e f : ℝ) (w : FrameSpace) : FrameSpace →L[ℝ] ℝ :=
  w 1 • fieldD (MvPolynomial.pderiv 0 G) e f w +
    firstAt G e f 0 (w 0) • coord 1 + fieldD (MvPolynomial.pderiv 1 G) e f w

private def zD (G : Poly) (e f : ℝ) (w : FrameSpace) : FrameSpace →L[ℝ] ℝ :=
  w 2 • fieldD (MvPolynomial.pderiv 0 G) e f w +
    firstAt G e f 0 (w 0) • coord 2 +
    (w 3 • fieldD (MvPolynomial.pderiv 1 G) e f w +
      firstAt G e f 1 (w 0) • coord 3) + fieldD (MvPolynomial.pderiv 2 G) e f w

private def yzD (G : Poly) (e f : ℝ) (w : FrameSpace) : FrameSpace →L[ℝ] ℝ :=
  (w 1 * w 2) • fieldD (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 G)) e f w +
    secondAt G e f 0 0 (w 0) • (w 1 • coord 2 + w 2 • coord 1) +
  ((w 1 * w 3 + w 2) • fieldD (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 G)) e f w +
    secondAt G e f 0 1 (w 0) • (w 1 • coord 3 + w 3 • coord 1 + coord 2)) +
  (w 1 • fieldD (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 G)) e f w +
    secondAt G e f 0 2 (w 0) • coord 1) +
  (w 3 • fieldD (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G)) e f w +
    secondAt G e f 1 1 (w 0) • coord 3) +
  fieldD (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G)) e f w

private def zzD (G : Poly) (e f : ℝ) (w : FrameSpace) : FrameSpace →L[ℝ] ℝ :=
  (w 2 * w 2) • fieldD (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 G)) e f w +
    secondAt G e f 0 0 (w 0) • (w 2 • coord 2 + w 2 • coord 2) +
  ((2 * w 2 * w 3) • fieldD (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 G)) e f w +
    secondAt G e f 0 1 (w 0) • ((2 * w 2) • coord 3 + w 3 • ((2 : ℝ) • coord 2))) +
  ((2 * w 2) • fieldD (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 G)) e f w +
    secondAt G e f 0 2 (w 0) • ((2 : ℝ) • coord 2)) +
  ((w 3 * w 3) • fieldD (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G)) e f w +
    secondAt G e f 1 1 (w 0) • (w 3 • coord 3 + w 3 • coord 3)) +
  ((2 * w 3) • fieldD (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G)) e f w +
    secondAt G e f 1 2 (w 0) • ((2 : ℝ) • coord 3)) +
  fieldD (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 G)) e f w

/-- The computed actual differential; c-column terms retain third derivatives. -/
def normalizationDifferentialI (G : Poly) (e f : ℝ) (w : FrameSpace) :
    FrameSpace →L[ℝ] FrameSpace :=
  ContinuousLinearMap.pi ![fieldD G e f w, yD G e f w, zD G e f w, yzD G e f w]

def normalizationDifferentialII (G : Poly) (e f : ℝ) (w : FrameSpace) :
    FrameSpace →L[ℝ] FrameSpace :=
  ContinuousLinearMap.pi ![fieldD G e f w, yD G e f w, zD G e f w, zzD G e f w]

private theorem hasFDerivAt_y (G : Poly) (e f : ℝ) (w : FrameSpace) :
    HasFDerivAt (fun u => MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (pullback u e f G)))
      (yD G e f w) w := by
  have h := ((hasFDerivAt_apply (𝕜 := ℝ) 1 w).mul (hasFDerivAt_field (MvPolynomial.pderiv 0 G) e f w)).add
    (hasFDerivAt_field (MvPolynomial.pderiv 1 G) e f w)
  simpa only [first_y, firstAt, yD, coord] using h

private theorem hasFDerivAt_z (G : Poly) (e f : ℝ) (w : FrameSpace) :
    HasFDerivAt (fun u => MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (pullback u e f G)))
      (zD G e f w) w := by
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) 2 w).mul (hasFDerivAt_field (MvPolynomial.pderiv 0 G) e f w)).add
    ((hasFDerivAt_apply (𝕜 := ℝ) 3 w).mul (hasFDerivAt_field (MvPolynomial.pderiv 1 G) e f w))).add
    (hasFDerivAt_field (MvPolynomial.pderiv 2 G) e f w)
  simpa only [first_z, firstAt, zD, coord] using h

private theorem hasFDerivAt_yz (G : Poly) (e f : ℝ) (w : FrameSpace) :
    HasFDerivAt (fun u => MvPolynomial.eval 0
      (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (pullback u e f G)))) (yzD G e f w) w := by
  have ha := hasFDerivAt_apply (𝕜 := ℝ) 1 w
  have hb := hasFDerivAt_apply (𝕜 := ℝ) 2 w
  have hd := hasFDerivAt_apply (𝕜 := ℝ) 3 w
  have h0 := (ha.mul hb).mul
    (hasFDerivAt_field (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 G)) e f w)
  have h1 := ((ha.mul hd).add hb).mul
    (hasFDerivAt_field (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 G)) e f w)
  have h2 := ha.mul
    (hasFDerivAt_field (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 G)) e f w)
  have h3 := hd.mul
    (hasFDerivAt_field (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G)) e f w)
  have h4 := hasFDerivAt_field (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G)) e f w
  have h01 := h0.add h1
  have h012 := h01.add h2
  have h0123 := h012.add h3
  have h := h0123.add h4
  simpa only [second_yz, secondAt, yzD, coord] using h

private theorem hasFDerivAt_zz (G : Poly) (e f : ℝ) (w : FrameSpace) :
    HasFDerivAt (fun u => MvPolynomial.eval 0
      (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (pullback u e f G)))) (zzD G e f w) w := by
  have hb := hasFDerivAt_apply (𝕜 := ℝ) 2 w
  have hd := hasFDerivAt_apply (𝕜 := ℝ) 3 w
  have h0 := (hb.mul hb).mul
    (hasFDerivAt_field (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 G)) e f w)
  have h1 := ((hb.const_mul 2).mul hd).mul
    (hasFDerivAt_field (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 G)) e f w)
  have h2 := (hb.const_mul 2).mul
    (hasFDerivAt_field (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 G)) e f w)
  have h3 := (hd.mul hd).mul
    (hasFDerivAt_field (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G)) e f w)
  have h4 := (hd.const_mul 2).mul
    (hasFDerivAt_field (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G)) e f w)
  have h5 := hasFDerivAt_field (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 G)) e f w
  have h01 := h0.add h1
  have h012 := h01.add h2
  have h0123 := h012.add h3
  have h01234 := h0123.add h4
  have h := h01234.add h5
  simpa only [second_zz, pow_two, secondAt, zzD, coord] using h

 theorem hasFDerivAt_normalizationEquationsI (G : Poly) (e f : ℝ) (w : FrameSpace) :
    HasFDerivAt (normalizationEquationsI G e f) (normalizationDifferentialI G e f w) w := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa only [normalizationEquationsI, normalizationDifferentialI, Matrix.cons_val_zero,
      eval_pullback_zero] using hasFDerivAt_field G e f w
  · simpa only [normalizationEquationsI, normalizationDifferentialI, Matrix.cons_val_succ,
      Matrix.cons_val_zero] using hasFDerivAt_y G e f w
  · simpa only [normalizationEquationsI, normalizationDifferentialI, Matrix.cons_val_succ,
      Matrix.cons_val_zero] using hasFDerivAt_z G e f w
  · simpa only [normalizationEquationsI, normalizationDifferentialI, Matrix.cons_val_succ,
      Matrix.cons_val_zero] using hasFDerivAt_yz G e f w

 theorem hasFDerivAt_normalizationEquationsII (G : Poly) (e f : ℝ) (w : FrameSpace) :
    HasFDerivAt (normalizationEquationsII G e f) (normalizationDifferentialII G e f w) w := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa only [normalizationEquationsII, normalizationDifferentialII, Matrix.cons_val_zero,
      eval_pullback_zero] using hasFDerivAt_field G e f w
  · simpa only [normalizationEquationsII, normalizationDifferentialII, Matrix.cons_val_succ,
      Matrix.cons_val_zero] using hasFDerivAt_y G e f w
  · simpa only [normalizationEquationsII, normalizationDifferentialII, Matrix.cons_val_succ,
      Matrix.cons_val_zero] using hasFDerivAt_z G e f w
  · simpa only [normalizationEquationsII, normalizationDifferentialII, Matrix.cons_val_succ,
      Matrix.cons_val_zero] using hasFDerivAt_zz G e f w

private theorem differentialI_basis1 (G : Poly) (e f : ℝ) (w : FrameSpace) :
    normalizationDifferentialI G e f w (Pi.single 1 1) =
      ![0, firstAt G e f 0 (w 0), 0, w 2 * secondAt G e f 0 0 (w 0) + w 3 * secondAt G e f 0 1 (w 0) + secondAt G e f 0 2 (w 0)] := by
  ext i
  fin_cases i <;>
    simp [normalizationDifferentialI, fieldD, yD, zD, yzD, coord]
  all_goals ring

private theorem differentialI_basis2 (G : Poly) (e f : ℝ) (w : FrameSpace) :
    normalizationDifferentialI G e f w (Pi.single 2 1) =
      ![0, 0, firstAt G e f 0 (w 0), w 1 * secondAt G e f 0 0 (w 0) + secondAt G e f 0 1 (w 0)] := by
  ext i
  fin_cases i <;>
    simp [normalizationDifferentialI, fieldD, yD, zD, yzD, coord]
  all_goals ring

private theorem differentialI_basis3 (G : Poly) (e f : ℝ) (w : FrameSpace) :
    normalizationDifferentialI G e f w (Pi.single 3 1) =
      ![0, 0, firstAt G e f 1 (w 0), w 1 * secondAt G e f 0 1 (w 0) + secondAt G e f 1 1 (w 0)] := by
  ext i
  fin_cases i <;>
    simp [normalizationDifferentialI, fieldD, yD, zD, yzD, coord]
  all_goals ring

private theorem differentialII_basis1 (G : Poly) (e f : ℝ) (w : FrameSpace) :
    normalizationDifferentialII G e f w (Pi.single 1 1) =
      ![0, firstAt G e f 0 (w 0), 0, 0] := by
  ext i
  fin_cases i <;>
    simp [normalizationDifferentialII, fieldD, yD, zD, zzD, coord]

private theorem differentialII_basis2 (G : Poly) (e f : ℝ) (w : FrameSpace) :
    normalizationDifferentialII G e f w (Pi.single 2 1) =
      ![0, 0, firstAt G e f 0 (w 0), 2 * (w 2 * secondAt G e f 0 0 (w 0) + w 3 * secondAt G e f 0 1 (w 0) + secondAt G e f 0 2 (w 0))] := by
  ext i
  fin_cases i <;>
    simp [normalizationDifferentialII, fieldD, yD, zD, zzD, coord]
  all_goals ring

private theorem differentialII_basis3 (G : Poly) (e f : ℝ) (w : FrameSpace) :
    normalizationDifferentialII G e f w (Pi.single 3 1) =
      ![0, 0, firstAt G e f 1 (w 0), 2 * (w 2 * secondAt G e f 0 1 (w 0) + w 3 * secondAt G e f 1 1 (w 0) + secondAt G e f 1 2 (w 0))] := by
  ext i
  fin_cases i <;>
    simp [normalizationDifferentialII, fieldD, yD, zD, zzD, coord]
  all_goals ring

/-- The actual Jacobian has the triangular normalization shape. The remaining
c-column entries are the actual fderiv entries, never assumptions. -/
theorem ordinaryJacobian_normalizationEquationsI (G : Poly) (e f : ℝ) (w : FrameSpace) :
    ordinaryJacobian (normalizationEquationsI G e f) w =
      normalizationMatrix (firstAt G e f 0 (w 0)) (firstAt G e f 1 (w 0))
        (ordinaryJacobian (normalizationEquationsI G e f) w 1 0)
        (ordinaryJacobian (normalizationEquationsI G e f) w 2 0)
        (ordinaryJacobian (normalizationEquationsI G e f) w 3 0)
        (w 2 * secondAt G e f 0 0 (w 0) + w 3 * secondAt G e f 0 1 (w 0) +
          secondAt G e f 0 2 (w 0))
        (w 1 * secondAt G e f 0 0 (w 0) + secondAt G e f 0 1 (w 0))
        (w 1 * secondAt G e f 0 1 (w 0) + secondAt G e f 1 1 (w 0)) := by
  have hd := (hasFDerivAt_normalizationEquationsI G e f w).fderiv
  ext i j
  simp only [ordinaryJacobian, hd]
  fin_cases j
  · fin_cases i <;>
      simp [normalizationMatrix, normalizationDifferentialI, fieldD, coord]
  · change normalizationDifferentialI G e f w (Pi.single 1 1) i = _
    rw [differentialI_basis1 G e f w]
    fin_cases i <;> simp [normalizationMatrix]
  · change normalizationDifferentialI G e f w (Pi.single 2 1) i = _
    rw [differentialI_basis2 G e f w]
    fin_cases i <;> simp [normalizationMatrix]
  · change normalizationDifferentialI G e f w (Pi.single 3 1) i = _
    rw [differentialI_basis3 G e f w]
    fin_cases i <;> simp [normalizationMatrix]

/-- Chart II uses the literal zz equation, including its factor two. -/
theorem ordinaryJacobian_normalizationEquationsII (G : Poly) (e f : ℝ) (w : FrameSpace) :
    ordinaryJacobian (normalizationEquationsII G e f) w =
      normalizationMatrix (firstAt G e f 0 (w 0)) (firstAt G e f 1 (w 0))
        (ordinaryJacobian (normalizationEquationsII G e f) w 1 0)
        (ordinaryJacobian (normalizationEquationsII G e f) w 2 0)
        (ordinaryJacobian (normalizationEquationsII G e f) w 3 0) 0
        (2 * (w 2 * secondAt G e f 0 0 (w 0) + w 3 * secondAt G e f 0 1 (w 0) +
          secondAt G e f 0 2 (w 0)))
        (2 * (w 2 * secondAt G e f 0 1 (w 0) + w 3 * secondAt G e f 1 1 (w 0) +
          secondAt G e f 1 2 (w 0))) := by
  have hd := (hasFDerivAt_normalizationEquationsII G e f w).fderiv
  ext i j
  simp only [ordinaryJacobian, hd]
  fin_cases j
  · fin_cases i <;>
      simp [normalizationMatrix, normalizationDifferentialII, fieldD, coord]
  · change normalizationDifferentialII G e f w (Pi.single 1 1) i = _
    rw [differentialII_basis1 G e f w]
    fin_cases i <;> simp [normalizationMatrix]
  · change normalizationDifferentialII G e f w (Pi.single 2 1) i = _
    rw [differentialII_basis2 G e f w]
    fin_cases i <;> simp [normalizationMatrix]
  · change normalizationDifferentialII G e f w (Pi.single 3 1) i = _
    rw [differentialII_basis3 G e f w]
    fin_cases i <;> simp [normalizationMatrix]

end PaperI.NormalFibers
