import PaperILean.NormalJacobianDifferential
import PaperILean.PolynomialDifferentiation

/-! I2379[0,131): the actual Gauss-H normalization differential.
The source coordinates are (Tx,Ty,C,D), and the full polynomial is retained.
No normalization matrix or derivative identity is assumed. -/

noncomputable section
namespace PaperI.GaussHDerivative

open PaperI.NormalFibers

/-- Actual H action: (x,y,z) maps to (x+q2*z+q0,y+q3*z+q1,z). -/
noncomputable def Hmap (G : Poly) (q : FrameSpace) : FrameSpace :=
  normalizationEquationsI G (q 1) 0 ![q 0, 0, q 2, q 3]

/-- Ordinary Jacobian in the manuscript's body-column order (Tx,Ty,C,D). -/
noncomputable def rawHJacobian (G : Poly) : Matrix (Fin 4) (Fin 4) ℝ :=
  ordinaryJacobian (Hmap G) 0

private def center : FrameSpace →L[ℝ] PhysicalSpace :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1, 0]

private theorem center_apply (q : FrameSpace) : center q = ![q 0, q 1, 0] := by
  ext i
  fin_cases i <;> simp [center]

private def ev (P : Poly) (q : FrameSpace) : ℝ := MvPolynomial.eval (center q) P

private def evD (P : Poly) : FrameSpace →L[ℝ] ℝ :=
  (polynomialDifferential P 0).comp center

private theorem hasFDerivAt_ev (P : Poly) : HasFDerivAt (ev P) (evD P) 0 := by
  have h := (hasFDerivAt_evalPolynomial P (center 0)).comp 0 center.hasFDerivAt
  simpa only [map_zero, Function.comp_def, ev, evD] using h

private theorem Hmap_eq_ev (G : Poly) (q : FrameSpace) :
    Hmap G q =
      ![ev G q, ev (MvPolynomial.pderiv 1 G) q,
        q 2 * ev (MvPolynomial.pderiv 0 G) q +
          q 3 * ev (MvPolynomial.pderiv 1 G) q + ev (MvPolynomial.pderiv 2 G) q,
        q 2 * ev (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 G)) q +
          q 3 * ev (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G)) q +
          ev (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G)) q] := by
  ext i
  fin_cases i <;>
    simp only [Hmap, normalizationEquationsI, Matrix.cons_val_zero,
      Matrix.cons_val_succ, eval_pullback_zero, first_y, first_z, second_yz]
  all_goals simp [
      ev, center_apply, firstAt, secondAt, valueAt]

theorem Hmap_zero (G : Poly) : Hmap G 0 =
    ![MvPolynomial.eval 0 G, MvPolynomial.eval 0 (MvPolynomial.pderiv 1 G),
      MvPolynomial.eval 0 (MvPolynomial.pderiv 2 G),
      MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G))] := by
  rw [Hmap_eq_ev]
  simp [ev]

/-- The differential of the actual H normalization map at the identity. -/
noncomputable def Hdifferential (G : Poly) : FrameSpace →L[ℝ] FrameSpace :=
  ContinuousLinearMap.pi ![evD G, evD (MvPolynomial.pderiv 1 G),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 0 G) • ContinuousLinearMap.proj 2 +
      MvPolynomial.eval 0 (MvPolynomial.pderiv 1 G) • ContinuousLinearMap.proj 3 +
      evD (MvPolynomial.pderiv 2 G),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 G)) •
        ContinuousLinearMap.proj 2 +
      MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G)) •
        ContinuousLinearMap.proj 3 +
      evD (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G))]

theorem hasFDerivAt_Hmap_zero (G : Poly) : HasFDerivAt (Hmap G) (Hdifferential G) 0 := by
  have hC := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) (0 : FrameSpace)
  have hD := hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) (0 : FrameSpace)
  have hz := ((hC.mul (hasFDerivAt_ev (MvPolynomial.pderiv 0 G))).add
    (hD.mul (hasFDerivAt_ev (MvPolynomial.pderiv 1 G)))).add
    (hasFDerivAt_ev (MvPolynomial.pderiv 2 G))
  have hyz := ((hC.mul (hasFDerivAt_ev (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 G)))).add
    (hD.mul (hasFDerivAt_ev (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G))))).add
    (hasFDerivAt_ev (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G)))
  have heq : Hmap G = fun q =>
      ![ev G q, ev (MvPolynomial.pderiv 1 G) q,
        q 2 * ev (MvPolynomial.pderiv 0 G) q +
          q 3 * ev (MvPolynomial.pderiv 1 G) q + ev (MvPolynomial.pderiv 2 G) q,
        q 2 * ev (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 G)) q +
          q 3 * ev (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G)) q +
          ev (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G)) q] := funext (Hmap_eq_ev G)
  rw [heq]
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa only [Hdifferential, Matrix.cons_val_zero] using hasFDerivAt_ev G
  · simpa only [Hdifferential, Matrix.cons_val_zero, Matrix.cons_val_succ] using
      hasFDerivAt_ev (MvPolynomial.pderiv 1 G)
  · simpa [Hdifferential, ev] using hz
  · simpa [Hdifferential, ev] using hyz

/-- Every entry of the raw matrix is the actual Frechet derivative of Hmap. -/
theorem rawHJacobian_eq_matrix (G : Poly) :
    rawHJacobian G =
      !![MvPolynomial.eval 0 (MvPolynomial.pderiv 0 G),
          MvPolynomial.eval 0 (MvPolynomial.pderiv 1 G), 0, 0;
        MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 G)),
          MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G)), 0, 0;
        MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 G)),
          MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G)),
          MvPolynomial.eval 0 (MvPolynomial.pderiv 0 G),
          MvPolynomial.eval 0 (MvPolynomial.pderiv 1 G);
        MvPolynomial.eval 0 (MvPolynomial.pderiv 0
          (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G))),
          MvPolynomial.eval 0 (MvPolynomial.pderiv 1
            (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G))),
          MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 G)),
          MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G))] := by
  unfold rawHJacobian ordinaryJacobian
  rw [(hasFDerivAt_Hmap_zero G).fderiv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hdifferential, evD, ContinuousLinearMap.comp_apply,
      polynomialDifferential_apply, center_apply, Fin.sum_univ_succ, Pi.single_apply]

end PaperI.GaussHDerivative
