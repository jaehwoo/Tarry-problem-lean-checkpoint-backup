import PaperILean.PolynomialLineTaylor
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! I3259 and I3269--I3274: the literal full polynomial in the source
upper-affine frame. Constants are retained. These identities are the bridge
from actual normalized frames to the finite-root counting argument. -/

noncomputable section
namespace PaperI.NormalFibers
open scoped BigOperators

abbrev Poly := MvPolynomial (Fin 3) ℝ

/-- Parameters are in the source order `(c,a,b,d)`. -/
def framePoint (w : Fin 4 → ℝ) (e f : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 0 + w 1 * x 1 + w 2 * x 2 + w 0, x 1 + w 3 * x 2 + e, x 2 + f]

def frameVariables (w : Fin 4 → ℝ) (e f : ℝ) : Fin 3 → Poly :=
  ![MvPolynomial.X 0 + MvPolynomial.C (w 1) * MvPolynomial.X 1 +
      MvPolynomial.C (w 2) * MvPolynomial.X 2 + MvPolynomial.C (w 0),
    MvPolynomial.X 1 + MvPolynomial.C (w 3) * MvPolynomial.X 2 + MvPolynomial.C e,
    MvPolynomial.X 2 + MvPolynomial.C f]

def pullback (w : Fin 4 → ℝ) (e f : ℝ) : Poly →ₐ[ℝ] Poly :=
  MvPolynomial.bind₁ (frameVariables w e f)

@[simp] theorem pullback_X (w : Fin 4 → ℝ) (e f : ℝ) (i : Fin 3) :
    pullback w e f (MvPolynomial.X i) = frameVariables w e f i := by
  simp [pullback]

@[simp] theorem pullback_C (w : Fin 4 → ℝ) (e f r : ℝ) :
    pullback w e f (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [pullback]

theorem eval_pullback (G : Poly) (w : Fin 4 → ℝ) (e f : ℝ) (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (pullback w e f G) = MvPolynomial.eval (framePoint w e f x) G := by
  change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C (frameVariables w e f) G) = _
  rw [← MvPolynomial.eval_assoc]
  have heq : (⇑(MvPolynomial.eval x) ∘ frameVariables w e f) = framePoint w e f x := by
    funext i
    fin_cases i <;> simp [frameVariables, framePoint]
  rw [heq]

@[simp] theorem eval_pullback_zero (G : Poly) (w : Fin 4 → ℝ) (e f : ℝ) :
    MvPolynomial.eval 0 (pullback w e f G) = MvPolynomial.eval ![w 0,e,f] G := by
  rw [eval_pullback]
  simp [framePoint]

theorem pullback_dx (G : Poly) (w : Fin 4 → ℝ) (e f : ℝ) :
    MvPolynomial.pderiv 0 (pullback w e f G) = pullback w e f (MvPolynomial.pderiv 0 G) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.pderiv_C]
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P j hP =>
      fin_cases j <;>
        simp [MvPolynomial.pderiv_mul, hP, frameVariables, MvPolynomial.pderiv_C]

theorem pullback_dy (G : Poly) (w : Fin 4 → ℝ) (e f : ℝ) :
    MvPolynomial.pderiv 1 (pullback w e f G) =
      MvPolynomial.C (w 1) * pullback w e f (MvPolynomial.pderiv 0 G) +
        pullback w e f (MvPolynomial.pderiv 1 G) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.pderiv_C]
  | add P Q hP hQ => simp [map_add, hP, hQ]; ring
  | mul_X P j hP =>
      fin_cases j <;>
        simp [MvPolynomial.pderiv_mul, hP, frameVariables, MvPolynomial.pderiv_C] <;> ring

theorem pullback_dz (G : Poly) (w : Fin 4 → ℝ) (e f : ℝ) :
    MvPolynomial.pderiv 2 (pullback w e f G) =
      MvPolynomial.C (w 2) * pullback w e f (MvPolynomial.pderiv 0 G) +
        MvPolynomial.C (w 3) * pullback w e f (MvPolynomial.pderiv 1 G) +
          pullback w e f (MvPolynomial.pderiv 2 G) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.pderiv_C]
  | add P Q hP hQ => simp [map_add, hP, hQ]; ring
  | mul_X P j hP =>
      fin_cases j <;>
        simp [MvPolynomial.pderiv_mul, hP, frameVariables, MvPolynomial.pderiv_C] <;> ring

theorem partial_commute (G : Poly) (i j : Fin 3) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j G) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i G) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.pderiv_C]
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P k hP =>
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        dsimp at hP <;>
        simp [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, Pi.single_apply, hP] <;> ring

def valueAt (G : Poly) (e f c : ℝ) : ℝ := MvPolynomial.eval ![c,e,f] G

def firstAt (G : Poly) (e f : ℝ) (i : Fin 3) (c : ℝ) : ℝ :=
  valueAt (MvPolynomial.pderiv i G) e f c

def secondAt (G : Poly) (e f : ℝ) (i j : Fin 3) (c : ℝ) : ℝ :=
  valueAt (MvPolynomial.pderiv i (MvPolynomial.pderiv j G)) e f c

theorem secondAt_commute (G : Poly) (e f c : ℝ) (i j : Fin 3) :
    secondAt G e f i j c = secondAt G e f j i c := by
  exact congrArg (fun P : Poly => valueAt P e f c) (partial_commute G i j)

theorem first_x (G : Poly) (w : Fin 4 → ℝ) (e f : ℝ) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (pullback w e f G)) =
      firstAt G e f 0 (w 0) := by
  rw [pullback_dx, eval_pullback_zero]
  rfl

theorem first_y (G : Poly) (w : Fin 4 → ℝ) (e f : ℝ) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (pullback w e f G)) =
      w 1 * firstAt G e f 0 (w 0) + firstAt G e f 1 (w 0) := by
  rw [pullback_dy]
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_pullback_zero]
  rfl

theorem first_z (G : Poly) (w : Fin 4 → ℝ) (e f : ℝ) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (pullback w e f G)) =
      w 2 * firstAt G e f 0 (w 0) + w 3 * firstAt G e f 1 (w 0) +
        firstAt G e f 2 (w 0) := by
  rw [pullback_dz]
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_pullback_zero]
  rfl

theorem second_yy (G : Poly) (w : Fin 4 → ℝ) (e f : ℝ) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (pullback w e f G))) =
      w 1 ^ 2 * secondAt G e f 0 0 (w 0) +
        2 * w 1 * secondAt G e f 0 1 (w 0) + secondAt G e f 1 1 (w 0) := by
  rw [pullback_dy]
  simp only [map_add, MvPolynomial.pderiv_C_mul, pullback_dy,
    MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_pullback_zero]
  change w 1 * (w 1 * secondAt G e f 0 0 (w 0) + secondAt G e f 1 0 (w 0)) +
    (w 1 * secondAt G e f 0 1 (w 0) + secondAt G e f 1 1 (w 0)) = _
  rw [secondAt_commute G e f (w 0) 1 0]
  ring

theorem second_yz (G : Poly) (w : Fin 4 → ℝ) (e f : ℝ) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (pullback w e f G))) =
      w 1 * w 2 * secondAt G e f 0 0 (w 0) +
        (w 1 * w 3 + w 2) * secondAt G e f 0 1 (w 0) +
          w 1 * secondAt G e f 0 2 (w 0) + w 3 * secondAt G e f 1 1 (w 0) +
            secondAt G e f 1 2 (w 0) := by
  rw [pullback_dz]
  simp only [map_add, MvPolynomial.pderiv_C_mul, pullback_dy,
    MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_pullback_zero]
  change w 2 * (w 1 * secondAt G e f 0 0 (w 0) + secondAt G e f 1 0 (w 0)) +
    w 3 * (w 1 * secondAt G e f 0 1 (w 0) + secondAt G e f 1 1 (w 0)) +
      (w 1 * secondAt G e f 0 2 (w 0) + secondAt G e f 1 2 (w 0)) = _
  rw [secondAt_commute G e f (w 0) 1 0]
  ring

theorem second_zz (G : Poly) (w : Fin 4 → ℝ) (e f : ℝ) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (pullback w e f G))) =
      w 2 ^ 2 * secondAt G e f 0 0 (w 0) +
        2 * w 2 * w 3 * secondAt G e f 0 1 (w 0) +
          2 * w 2 * secondAt G e f 0 2 (w 0) +
            w 3 ^ 2 * secondAt G e f 1 1 (w 0) +
              2 * w 3 * secondAt G e f 1 2 (w 0) + secondAt G e f 2 2 (w 0) := by
  rw [pullback_dz]
  simp only [map_add, MvPolynomial.pderiv_C_mul, pullback_dz,
    MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_pullback_zero]
  change w 2 * (w 2 * secondAt G e f 0 0 (w 0) + w 3 * secondAt G e f 1 0 (w 0) +
      secondAt G e f 2 0 (w 0)) +
    w 3 * (w 2 * secondAt G e f 0 1 (w 0) + w 3 * secondAt G e f 1 1 (w 0) +
      secondAt G e f 2 1 (w 0)) +
    (w 2 * secondAt G e f 0 2 (w 0) + w 3 * secondAt G e f 1 2 (w 0) +
      secondAt G e f 2 2 (w 0)) = _
  rw [secondAt_commute G e f (w 0) 1 0, secondAt_commute G e f (w 0) 2 0,
    secondAt_commute G e f (w 0) 2 1]
  ring

def linePolynomial (G : Poly) (e f : ℝ) : Polynomial ℝ :=
  PaperI.polynomialAlongLine G ![0,e,f] ![1,0,0]

@[simp] theorem linePolynomial_eval (G : Poly) (e f c : ℝ) :
    (linePolynomial G e f).eval c = valueAt G e f c := by
  rw [linePolynomial, PaperI.eval_polynomialAlongLine]
  have heq : (![0,e,f] : Fin 3 → ℝ) + c • ![1,0,0] = ![c,e,f] := by
    ext i
    fin_cases i <;> simp
  rw [heq]
  rfl

theorem linePolynomial_degree (G : Poly) (e f : ℝ) :
    (linePolynomial G e f).natDegree ≤ G.totalDegree :=
  PaperI.natDegree_polynomialAlongLine_le G _ _

theorem linePolynomial_derivative (G : Poly) (e f c : ℝ) :
    (linePolynomial G e f).derivative.eval c = firstAt G e f 0 c := by
  have hl : HasDerivAt (fun t : ℝ => (![t,e,f] : Fin 3 → ℝ)) ![1,0,0] c := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using hasDerivAt_id c
    · simpa using hasDerivAt_const c e
    · simpa using hasDerivAt_const c f
  have hg := (PaperI.hasFDerivAt_evalPolynomial G ![c,e,f]).comp_hasDerivAt c hl
  have hg' : HasDerivAt (fun t : ℝ => valueAt G e f t) (firstAt G e f 0 c) c := by
    simpa [PaperI.polynomialDifferential_apply, Fin.sum_univ_succ, firstAt, valueAt] using hg
  have hp : HasDerivAt (fun t : ℝ => valueAt G e f t)
      ((linePolynomial G e f).derivative.eval c) c := by
    simpa only [linePolynomial_eval] using (linePolynomial G e f).hasDerivAt c
  exact hp.unique hg'

/-- The literal source normalization, including constants and nonzero pivots. -/
def normalizedFrames (G : Poly) (e f : ℝ) : Set (Fin 4 → ℝ) :=
  {w | MvPolynomial.eval 0 (pullback w e f G) = 0 ∧
    MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (pullback w e f G)) ≠ 0 ∧
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (pullback w e f G)) = 0 ∧
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (pullback w e f G)) = 0 ∧
    ((MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (pullback w e f G))) = 0 ∧
      MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (pullback w e f G))) ≠ 0) ∨
     (MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (pullback w e f G))) = 0 ∧
      MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (pullback w e f G))) ≠ 0))}

end PaperI.NormalFibers
