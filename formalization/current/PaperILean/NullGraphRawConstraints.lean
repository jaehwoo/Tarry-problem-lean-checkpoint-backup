import PaperILean.OriginalNormalPolynomial
import PaperILean.NormalJacobianDifferential

/-! The four raw null constraints after the original affine pullback.
Only the parent phase constant is removed in the bracketed variant. -/

noncomputable section
namespace PaperI.NullGraphRawConstraints

open PaperI.NormalFibers

theorem iterated_x_pullback (P : Poly) (n : ℕ) (w : FrameSpace) (e f : ℝ) :
    iteratedPolynomialPartial n (fun _ => 0) (pullback w e f P) =
      pullback w e f (iteratedPolynomialPartial n (fun _ => 0) P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change MvPolynomial.pderiv 0
          (iteratedPolynomialPartial n (fun _ => 0) (pullback w e f P)) =
        pullback w e f
          (MvPolynomial.pderiv 0 (iteratedPolynomialPartial n (fun _ => 0) P))
      rw [ih, pullback_dx]

theorem iterated_x_sub_constant (P : Poly) (n : ℕ) (a : ℝ) :
    iteratedPolynomialPartial (n + 1) (fun _ => 0) (P - MvPolynomial.C a) =
      iteratedPolynomialPartial (n + 1) (fun _ => 0) P := by
  induction n with
  | zero => simp [iteratedPolynomialPartial, map_sub, MvPolynomial.pderiv_C]
  | succ n ih =>
      change MvPolynomial.pderiv 0
          (iteratedPolynomialPartial (n + 1) (fun _ => 0) (P - MvPolynomial.C a)) =
        MvPolynomial.pderiv 0
          (iteratedPolynomialPartial (n + 1) (fun _ => 0) P)
      rw [ih]

/-- Raw derivatives of the full pulled-back original parent phase, in the source row order. -/
def rawNullConstraints {k : ℕ} (J : CoefficientSpace k) (m : ℕ)
    (w : FrameSpace) : FrameSpace :=
  let H := iteratedPolynomialPartial (m - 1) (fun _ => 0)
    (pullback w 0 0 (coefficientPolynomial J))
  ![MvPolynomial.eval 0 H,
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 H),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 H),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 H))]

/-- The same raw derivatives with the parent phase bracketed before positive differentiation. -/
def bracketedRawNullConstraints {k : ℕ} (J : CoefficientSpace k) (m : ℕ)
    (w : FrameSpace) : FrameSpace :=
  let P := pullback w 0 0 (coefficientPolynomial J)
  let H := iteratedPolynomialPartial (m - 1) (fun _ => 0)
    (P - MvPolynomial.C (MvPolynomial.eval 0 P))
  ![MvPolynomial.eval 0 H,
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 H),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 H),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 H))]

theorem rawNullConstraints_eq {k : ℕ} (J : CoefficientSpace k) (m : ℕ) :
    rawNullConstraints J m = normalizationEquationsII (originalNormalPolynomial J (m - 1)) 0 0 := by
  funext w
  unfold rawNullConstraints normalizationEquationsII
  rw [iterated_x_pullback]
  rfl

theorem bracketedRawNullConstraints_eq_raw {k : ℕ} (J : CoefficientSpace k) (m : ℕ)
    (hm : 2 ≤ m) :
    bracketedRawNullConstraints J m = rawNullConstraints J m := by
  have horder : m - 1 = (m - 2) + 1 := by omega
  funext w
  unfold bracketedRawNullConstraints rawNullConstraints
  dsimp only
  rw [horder, iterated_x_sub_constant]

theorem bracketedRawNullConstraints_eq {k : ℕ} (J : CoefficientSpace k) (m : ℕ)
    (hm : 2 ≤ m) :
    bracketedRawNullConstraints J m =
      normalizationEquationsII (originalNormalPolynomial J (m - 1)) 0 0 := by
  rw [bracketedRawNullConstraints_eq_raw J m hm, rawNullConstraints_eq]

end PaperI.NullGraphRawConstraints
