import PaperILean.NecessitySeedJacobianDifferential
import PaperILean.AffineVectorFieldCoefficient
import PaperILean.PolynomialDerivativeCoefficients
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Paper II, II2472–II2489. All differential operators act on the actual
normalized upper-affine coefficient orbit of the original quartic. -/

open Filter
open scoped Topology BigOperators

noncomputable section
namespace PaperII.QuarticConnection

open PaperI MvPolynomial Matrix
abbrev Poly := MvPolynomial (Fin 3) ℝ
abbrev Plane := ℝ × ℝ

private def exponent (x y z : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 x + Finsupp.single 1 y + Finsupp.single 2 z

private theorem exponent_degree (x y z : ℕ) : (exponent x y z).degree = x + y + z := by
  simp [exponent, Finsupp.degree_add, Finsupp.degree_single]

private theorem exponent_injective {x y z X Y Z : ℕ}
    (h : exponent x y z = exponent X Y Z) : x = X ∧ y = Y ∧ z = Z := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [exponent] using congrArg (fun a : Fin 3 →₀ ℕ => a 0) h
  · simpa [exponent] using congrArg (fun a : Fin 3 →₀ ℕ => a 1) h
  · simpa [exponent] using congrArg (fun a : Fin 3 →₀ ℕ => a 2) h

private theorem exponent_eq_iff {x y z X Y Z : ℕ} :
    exponent x y z = exponent X Y Z ↔ x = X ∧ y = Y ∧ z = Z := by
  refine ⟨exponent_injective, ?_⟩
  rintro ⟨rfl, rfl, rfl⟩
  rfl

private theorem exponent_add (x y z X Y Z : ℕ) :
    exponent x y z + exponent X Y Z = exponent (x + X) (y + Y) (z + Z) := by
  simp only [exponent, Finsupp.single_add]
  abel

private theorem exponent_sub_y (x y z : ℕ) :
    exponent x (y+1) z - Finsupp.single 1 1 = exponent x y z := by
  ext i
  fin_cases i <;> simp [exponent]

private theorem exponent_sub_z (x y z : ℕ) :
    exponent x y (z+1) - Finsupp.single 2 1 = exponent x y z := by
  ext i
  fin_cases i <;> simp [exponent]

private theorem exponent_add_x (x y z : ℕ) :
    exponent x y z + Finsupp.single 0 1 = exponent (x+1) y z := by
  simp only [exponent, Finsupp.single_add]
  abel

private theorem exponent_add_y (x y z : ℕ) :
    exponent x y z + Finsupp.single 1 1 = exponent x (y+1) z := by
  simp only [exponent, Finsupp.single_add]
  abel

private theorem exponent_add_z (x y z : ℕ) :
    exponent x y z + Finsupp.single 2 1 = exponent x y (z+1) := by
  simp [exponent, Finsupp.single_add, add_assoc]

/-- Monomial coefficient in the ordinary power convention. -/
def coeffAt (x y z : ℕ) (J : Poly) : ℝ := coeff (exponent x y z) J

/-- The manuscript's row functional and denominator. -/
def connectionRow (B : ℝ) (J : Poly) : ℝ :=
  coeffAt 0 1 3 J - B / 3 * coeffAt 1 0 2 J

def connectionPivot (B : ℝ) (J : Poly) : ℝ :=
  2 * coeffAt 0 2 2 J - B / 3 * coeffAt 1 1 1 J

/-- The original generators A, D, and T_z, acting on polynomials. -/
def genA (J : Poly) : Poly := X 1 * pderiv 0 J
def genD (J : Poly) : Poly := X 2 * pderiv 1 J
def genTz (J : Poly) : Poly := pderiv 2 J

private theorem coeffAt_vanish (J : Poly) (hJ : J.totalDegree ≤ 4)
    (x y z : ℕ) (h : 4 < x+y+z) : coeffAt x y z J = 0 := by
  unfold coeffAt
  apply coeff_eq_zero_of_totalDegree_lt
  change J.totalDegree < (exponent x y z).degree
  rw [exponent_degree]
  exact hJ.trans_lt h

private theorem coeffAt_genA₁ (J : Poly) : coeffAt 0 1 3 (genA J) = coeffAt 1 0 3 J := by
  rw [coeffAt, genA, coeff_X_mul', if_pos, exponent_sub_y, coeff_polynomialPartial,
    exponent_add_x, coeffAt]
  · simp [exponent, Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (0 : Fin 3) ≠ 2 by decide]
  · simp [Finsupp.mem_support_iff, exponent, Finsupp.single_apply, Fin.reduceEq]

private theorem coeffAt_genA₂ (J : Poly) : coeffAt 1 0 2 (genA J) = 0 := by
  rw [coeffAt, genA, coeff_X_mul', if_neg]
  simp [Finsupp.mem_support_iff, exponent, Finsupp.single_apply, Fin.reduceEq]

private theorem coeffAt_genD₁ (J : Poly) : coeffAt 0 1 3 (genD J) = 2 * coeffAt 0 2 2 J := by
  rw [coeffAt, genD, coeff_X_mul', if_pos, exponent_sub_z, coeff_polynomialPartial,
    exponent_add_y, coeffAt]
  · simp [exponent, Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (0 : Fin 3) ≠ 2 by decide]
  · simp [Finsupp.mem_support_iff, exponent, Finsupp.single_apply, Fin.reduceEq]

private theorem coeffAt_genD₂ (J : Poly) : coeffAt 1 0 2 (genD J) = coeffAt 1 1 1 J := by
  rw [coeffAt, genD, coeff_X_mul', if_pos, exponent_sub_z, coeff_polynomialPartial,
    exponent_add_y, coeffAt]
  · simp [exponent, Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (0 : Fin 3) ≠ 2 by decide]
  · simp [Finsupp.mem_support_iff, exponent, Finsupp.single_apply, Fin.reduceEq]

private theorem coeffAt_genTz₁ (J : Poly) :
    coeffAt 0 1 3 (genTz J) = 4 * coeffAt 0 1 4 J := by
  rw [coeffAt, genTz, coeff_polynomialPartial, exponent_add_z, coeffAt]
  simp [exponent, Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (0 : Fin 3) ≠ 2 by decide]

private theorem coeffAt_genTz₂ (J : Poly) :
    coeffAt 1 0 2 (genTz J) = 3 * coeffAt 1 0 3 J := by
  rw [coeffAt, genTz, coeff_polynomialPartial, exponent_add_z, coeffAt]
  simp [exponent, Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (0 : Fin 3) ≠ 2 by decide]

/-- II2480: the indicated functional annihilates BA+T_z on every quartic
and evaluates to the indicated pivot on D. -/
theorem quartic_operator_rows (B : ℝ) (J : Poly) (hJ : J.totalDegree ≤ 4) :
    connectionRow B (C B * genA J + genTz J) = 0 ∧
    connectionRow B (genD J) = connectionPivot B J := by
  have hhigh := coeffAt_vanish J hJ 0 1 4 (by decide)
  constructor
  · have hrows (x y z : ℕ) : coeffAt x y z (C B * genA J + genTz J) =
        B * coeffAt x y z (genA J) + coeffAt x y z (genTz J) := by
      simp [coeffAt]
    rw [connectionRow, hrows, hrows, coeffAt_genA₁, coeffAt_genA₂, coeffAt_genTz₁,
      coeffAt_genTz₂, hhigh]
    ring
  · rw [connectionRow, coeffAt_genD₁, coeffAt_genD₂, connectionPivot]

/-- The compact normalized null model, including its arbitrary affine
tangential terms. -/
def nullModel (a r B Ly Lz L0 : ℝ) : Poly :=
  C a * (X 0 - C (r / 2) * X 1 ^ 2 - C B * X 1 * X 2) ^ 2 +
    C Ly * X 1 + C Lz * X 2 + C L0

private theorem nullModel_square (r B : ℝ) :
    (X (0 : Fin 3) - C (r / 2) * X 1 ^ 2 - C B * X 1 * X 2 : Poly)^2 =
      monomial (exponent 2 0 0) 1 +
      monomial (exponent 1 2 0) (-r) +
      monomial (exponent 1 1 1) (-2*B) +
      monomial (exponent 0 4 0) ((r/2)^2) +
      monomial (exponent 0 3 1) (r*B) +
      monomial (exponent 0 2 2) (B^2) := by
  have h0 : X (0 : Fin 3) = monomial (exponent 1 0 0) (1 : ℝ) := by simp [X, exponent]
  have h1 : X (1 : Fin 3) = monomial (exponent 0 1 0) (1 : ℝ) := by simp [X, exponent]
  have h2 : X (2 : Fin 3) = monomial (exponent 0 0 1) (1 : ℝ) := by simp [X, exponent]
  have hC (b : ℝ) : C b = (monomial (0 : Fin 3 →₀ ℕ)) b := rfl
  have hm (x y z : ℕ) (a b : ℝ) :
      C a * monomial (exponent x y z) b = monomial (exponent x y z) (a*b) := by
    rw [hC, monomial_mul, zero_add]
  have hN : C (r/2) * X (1 : Fin 3) ^ 2 = monomial (exponent 0 2 0) (r/2) := by
    rw [h1, pow_two, monomial_mul, exponent_add, hm]
    simp
  have hO : C B * X (1 : Fin 3) * X (2 : Fin 3) = monomial (exponent 0 1 1) B := by
    rw [h1, h2, hm, monomial_mul, exponent_add]
    simp
  have hsq (u v w : Poly) :
      (u-v-w)^2 = u*u - (u*v+u*v) - (u*w+u*w) + v*v + (v*w+v*w) + w*w := by ring
  rw [hN, hO, h0, hsq]
  simp only [monomial_mul, exponent_add]
  have hadd (d : Fin 3 →₀ ℕ) (a b : ℝ) :
      monomial d a + monomial d b = monomial d (a+b) := (map_add _ _ _).symm
  have hneg (d : Fin 3 →₀ ℕ) (a : ℝ) :
      -monomial d a = monomial d (-a) := (map_neg _ _).symm
  simp only [sub_eq_add_neg, hadd, hneg]
  ring_nf

/-- The two literal coefficients yield the exact compact model pivot. -/
theorem nullModel_connectionPivot (a r B Ly Lz L0 : ℝ) :
    connectionPivot B (nullModel a r B Ly Lz L0) = (8/3 : ℝ) * a * B^2 := by
  rw [connectionPivot, nullModel, nullModel_square]
  simp only [coeffAt, coeff_add, coeff_C_mul, coeff_monomial, exponent_eq_iff]
  have hz : (0 : Fin 3 →₀ ℕ) = exponent 0 0 0 := by simp [exponent]
  have h1 : X (1 : Fin 3) = monomial (exponent 0 1 0) (1 : ℝ) := by simp [X, exponent]
  have h2 : X (2 : Fin 3) = monomial (exponent 0 0 1) (1 : ℝ) := by simp [X, exponent]
  rw [h1, h2]
  simp [coeff_monomial, coeff_C, hz, exponent_eq_iff]
  ring

/-- In the original coordinates the chosen characteristic is (y(s),s). -/
def characteristicPoint (y : ℝ → ℝ) (s : ℝ) : Plane := (y s, s)

def graphPartial (c : Plane → ℝ) (w : Plane) (p : Plane) : ℝ := fderiv ℝ c p w

def graphY (c : Plane → ℝ) : Plane → ℝ := graphPartial c (1,0)
def graphZ (c : Plane → ℝ) : Plane → ℝ := graphPartial c (0,1)
def graphYY (c : Plane → ℝ) : Plane → ℝ := graphY (graphY c)
def graphYZ (c : Plane → ℝ) : Plane → ℝ := graphZ (graphY c)
def graphZZ (c : Plane → ℝ) : Plane → ℝ := graphZ (graphZ c)

def mixedCurvature (c d : Plane → ℝ) (p : Plane) : ℝ :=
  graphYZ c p + d p * graphYY c p

def nullRate (d : Plane → ℝ) (p : Plane) : ℝ := fderiv ℝ d p (d p, 1)

def tangentFrame (c d : Plane → ℝ) (p : Plane) : Fin 6 → ℝ :=
  ![graphY c p, graphZ c p + d p * graphY c p, c p, d p, p.1, p.2]

def tangentVelocity (a B b d v : ℝ) : Fin 6 → ℝ := ![B, v*a, b, v, d, 1]

private theorem direction_decomposition (L : Plane →L[ℝ] ℝ) (r : ℝ) :
    L (r, 1) = r * L (1,0) + L (0,1) := by
  have he : (r, 1) = r • ((1,0) : Plane) + (0,1) := by ext <;> simp
  rw [he, map_add, map_smul]
  rfl

private theorem graph_partial_derivative {c : Plane → ℝ} {p w : Plane}
    (hc : ContDiffAt ℝ 2 c p) :
    DifferentiableAt ℝ (graphPartial c w) p := by
  have h := (hc.fderiv_right (m := 1) (by norm_num)).clm_apply (contDiffAt_const (c := w))
  exact h.differentiableAt le_rfl

private theorem graph_mixed_symmetric {c : Plane → ℝ} {p : Plane}
    (hc : ContDiffAt ℝ 2 c p) : graphY (graphZ c) p = graphYZ c p := by
  have h := (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  change fderiv ℝ (fun q => fderiv ℝ c q (0, 1)) p (1, 0) =
    fderiv ℝ (fun q => fderiv ℝ c q (1, 0)) p (0, 1)
  rw [fderiv_clm_apply h (differentiableAt_const _),
    fderiv_clm_apply h (differentiableAt_const _)]
  simp only [fderiv_const, ContinuousLinearMap.zero_apply, map_zero, add_zero]
  simpa using hc.isSymmSndFDerivAt (by simp) (1,0) (0,1)

/-- Differentiate the actual six coordinates using the selected null equation. -/
theorem tangentFrame_hasDerivAt
    (c d : Plane → ℝ) (y : ℝ → ℝ) (s : ℝ)
    (hc : ContDiffAt ℝ 2 c (characteristicPoint y s))
    (hd : DifferentiableAt ℝ d (characteristicPoint y s))
    (hy : HasDerivAt y (d (characteristicPoint y s)) s)
    (hnull : graphZZ c (characteristicPoint y s) +
        2 * d (characteristicPoint y s) * graphYZ c (characteristicPoint y s) +
        d (characteristicPoint y s)^2 * graphYY c (characteristicPoint y s) = 0) :
    let p := characteristicPoint y s
    let g := fun q => tangentFrame c d (characteristicPoint y q)
    HasDerivAt g
      (tangentVelocity (graphY c p) (mixedCurvature c d p)
        (graphZ c p + d p * graphY c p) (d p) (nullRate d p)) s := by
  dsimp only
  let p := characteristicPoint y s
  have hp : HasDerivAt (characteristicPoint y) (d p, 1) s :=
    hy.prodMk (hasDerivAt_id s)
  have ha := ((graph_partial_derivative (w := (1,0)) hc).hasFDerivAt).comp_hasDerivAt s hp
  have haz : HasDerivAt (fun t => graphY c (characteristicPoint y t))
      (mixedCurvature c d p) s := by
    change HasDerivAt (fun t => graphY c (characteristicPoint y t))
      (fderiv ℝ (graphY c) p (0,1) + d p * fderiv ℝ (graphY c) p (1,0)) s
    rw [add_comm, ← direction_decomposition]
    exact ha
  have hz := ((graph_partial_derivative (w := (0,1)) hc).hasFDerivAt).comp_hasDerivAt s hp
  have hzz : HasDerivAt (fun t => graphZ c (characteristicPoint y t))
      (d p * graphYZ c p + graphZZ c p) s := by
    have heq : fderiv ℝ (graphZ c) p (d p, 1) =
        d p * graphYZ c p + graphZZ c p := by
      rw [direction_decomposition]
      change d p * graphY (graphZ c) p + graphZZ c p = _
      rw [graph_mixed_symmetric hc]
    rw [← heq]
    exact hz
  have hv : HasDerivAt (fun t => d (characteristicPoint y t)) (nullRate d p) s :=
    hd.hasFDerivAt.comp_hasDerivAt s hp
  have hb0 := hzz.add (hv.mul haz)
  have hb : HasDerivAt (fun t => graphZ c (characteristicPoint y t) +
      d (characteristicPoint y t) * graphY c (characteristicPoint y t))
      (nullRate d p * graphY c p) s := by
    convert hb0 using 1
    dsimp only [p] at *
    unfold mixedCurvature
    linarith [hnull, show d (characteristicPoint y s) *
        (d (characteristicPoint y s) * graphYY c (characteristicPoint y s)) =
        d (characteristicPoint y s)^2 * graphYY c (characteristicPoint y s) by ring]
  have hcenter : HasDerivAt (fun t => c (characteristicPoint y t))
      (graphZ c p + d p * graphY c p) s := by
    change HasDerivAt (fun t => c (characteristicPoint y t))
      (fderiv ℝ c p (0,1) + d p * fderiv ℝ c p (1,0)) s
    rw [add_comm, ← direction_decomposition]
    exact (hc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s hp
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i <;> simp only [tangentFrame, tangentVelocity, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_one]
  · exact haz
  · exact hb
  · exact hcenter
  · exact hv
  · exact hy
  · exact hasDerivAt_id s

private def upperCenter (g : Fin 6 → ℝ) : PhysicalSpace := ![g 2,g 4,g 5]

private def upperLinear (g : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,g 0,g 1;0,1,g 3;0,0,1]

private def connectionTranslation : PhysicalSpace := ![0,0,1]

private def connectionLinear (B v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0,B,0;0,0,v;0,0,0]

/-- The moving normalized phase and its quartic polynomial representative. -/
def normalizedQuartic (F : CoefficientSpace 4) (c d : Plane → ℝ) (y : ℝ → ℝ)
    (s : ℝ) : CoefficientSpace 4 :=
  let g := tangentFrame c d (characteristicPoint y s)
  affineCoefficientMap 4 (upperCenter g) (upperLinear g) F

def nullGenerator (B v : ℝ) (J : Poly) : Poly :=
  C B * genA J + genTz J + C v * genD J

private theorem nullGenerator_coeff (B v : ℝ) (J : Poly) (hJ : J.totalDegree ≤ 4) :
    connectionRow B (nullGenerator B v J) = v * connectionPivot B J := by
  have ha := (quartic_operator_rows B J hJ).1
  have hd := (quartic_operator_rows B J hJ).2
  unfold connectionRow coeffAt at *
  simp only [nullGenerator, coeff_add, coeff_C_mul] at *
  linarith only [ha, congrArg (fun u : ℝ => v*u) hd]

private theorem nullGenerator_eq_affineFieldPolynomialMap (B v : ℝ) (J : Poly) :
    affineFieldPolynomialMap connectionTranslation (connectionLinear B v) J = nullGenerator B v J := by
  rw [affineFieldPolynomialMap_apply, Fin.sum_univ_three]
  simp [connectionTranslation, connectionLinear, affineCoordinate,
    Fin.sum_univ_three, nullGenerator, genA, genD, genTz]
  ring

private def index4 (x y z : ℕ) (h1 : 1 ≤ x + y + z) (h4 : x + y + z ≤ 4) :
    MonomialIndex 4 :=
  (monomialIndexEquiv 4).symm ⟨exponent x y z, by
    change 1 ≤ (exponent x y z).degree ∧ (exponent x y z).degree ≤ 4
    rw [exponent_degree]
    exact ⟨h1,h4⟩⟩

private theorem index4_exponent (x y z : ℕ) (h1 : 1 ≤ x + y + z) (h4 : x + y + z ≤ 4) :
    monomialExponent (index4 x y z h1 h4) = exponent x y z := by
  exact congrArg Subtype.val ((monomialIndexEquiv 4).apply_symm_apply _)

private theorem coeffAt_coeffSpace (F : CoefficientSpace 4)
    (x y z : ℕ) (h1 : 1 ≤ x + y + z) (h4 : x + y + z ≤ 4) :
    coeffAt x y z (coefficientPolynomial F) = F (index4 x y z h1 h4) := by
  rw [coeffAt, ← index4_exponent x y z h1 h4]
  have hi : Function.Injective (@monomialExponent 4) :=
    fun _ _ h => (monomialIndexEquiv 4).injective (Subtype.ext h)
  rw [coefficientPolynomial_eq_sum, coeff_sum]
  simp only [coeff_monomial, hi.eq_iff]
  rw [Finset.sum_eq_single (index4 x y z h1 h4)]
  · simp
  · intro i _ hine
    have hne : monomialExponent i ≠ monomialExponent (index4 x y z h1 h4) :=
      fun h => hine (hi h)
    simp [hne]
  · simp

private theorem upperOrbit_contDiff (F : CoefficientSpace 4) :
    ContDiff ℝ ⊤ (fun g : Fin 6 → ℝ => affineCoefficientMap 4 (upperCenter g) (upperLinear g) F) := by
  have hc : ContDiff ℝ ⊤ upperCenter := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [upperCenter] <;> fun_prop
  have hB : ContDiff ℝ ⊤ (fun g : Fin 6 → ℝ => fun i j : Fin 3 => upperLinear g i j) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp [upperLinear] <;> fun_prop
  exact NecessitySeedJacobian.contDiff_affineCoefficientMap_joint
    upperCenter upperLinear (fun _ => F) hc hB contDiff_const

private theorem upperPoint_hasDerivAt
    (g : ℝ → Fin 6 → ℝ) (s a B b d v : ℝ) (x : PhysicalSpace)
    (hg : HasDerivAt g (tangentVelocity a B b d v) s)
    (ha : g s 0 = a) (hb : g s 1 = b) (hd : g s 3 = d) :
    HasDerivAt (fun t => affinePoint (upperCenter (g t)) (upperLinear (g t)) x)
      (upperLinear (g s) *ᵥ (connectionTranslation + connectionLinear B v *ᵥ x)) s := by
  have h := hasDerivAt_pi.mp hg
  have hvel : upperLinear (g s) *ᵥ (connectionTranslation + connectionLinear B v *ᵥ x) =
      ![B*x 1+(v*a)*x 2+b,v*x 2+d,1] := by
    ext i
    fin_cases i <;>
      simp [upperLinear, connectionTranslation, connectionLinear, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three, ha, hb, hd] <;> ring
  rw [hvel]
  have hcoord : (fun t => affinePoint (upperCenter (g t)) (upperLinear (g t)) x) =
      (fun t => ![x 0 + g t 0 * x 1 + g t 1 * x 2 + g t 2,
        x 1 + g t 3 * x 2 + g t 4, x 2 + g t 5]) := by
    funext t
    ext i
    fin_cases i <;>
      simp [affinePoint, upperCenter, upperLinear, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three] <;> ring
  rw [hcoord]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [tangentVelocity] using
      ((((h 0).mul_const (x 1)).const_add (x 0)).add ((h 1).mul_const (x 2))).add (h 2)
  · simpa [tangentVelocity] using (((h 3).mul_const (x 2)).const_add (x 1)).add (h 4)
  · simpa [tangentVelocity] using (h 5).const_add (x 2)

private theorem upperOrbit_hasDerivAt
    (F : CoefficientSpace 4) (g : ℝ → Fin 6 → ℝ) (s a B b d v : ℝ)
    (hg : HasDerivAt g (tangentVelocity a B b d v) s)
    (ha : g s 0 = a) (hb : g s 1 = b) (hd : g s 3 = d) :
    HasDerivAt (fun t => affineCoefficientMap 4 (upperCenter (g t)) (upperLinear (g t)) F)
      (affineFieldCoefficientMap 4 connectionTranslation (connectionLinear B v)
        (affineCoefficientMap 4 (upperCenter (g s)) (upperLinear (g s)) F)) s := by
  let J := fun t => affineCoefficientMap 4 (upperCenter (g t)) (upperLinear (g t)) F
  have hJ : DifferentiableAt ℝ J s :=
    ((upperOrbit_contDiff F).differentiable (by simp) _).comp s hg.differentiableAt
  have hJ' := hJ.hasDerivAt
  have heq : deriv J s = affineFieldCoefficientMap 4 connectionTranslation (connectionLinear B v) (J s) := by
    apply coefficient_ext
    intro x
    let ev := NecessitySeedJacobian.phaseEvaluation 4 x
    have h1 := ev.hasFDerivAt.comp_hasDerivAt s hJ'
    have h2 := (hasFDerivAt_phase F _).comp_hasDerivAt s
      (upperPoint_hasDerivAt g s a B b d v x hg ha hb hd)
    have h3 := (hasFDerivAt_phase F _).comp_hasDerivAt s
      (upperPoint_hasDerivAt g s a B b d v 0 hg ha hb hd)
    have hp := h2.sub h3
    have hfun : (fun t => phase F (affinePoint (upperCenter (g t)) (upperLinear (g t)) x) -
        phase F (affinePoint (upperCenter (g t)) (upperLinear (g t)) 0)) =
        fun t => ev (J t) := by
      funext t
      simp [ev, J, NecessitySeedJacobian.phaseEvaluation_apply, PaperI.AllDim.phase_three,
        phase_affineCoefficientMap, affinePoint_zero]
    have hv := h1.unique (hfun ▸ hp)
    change phase (deriv J s) x = _
    have hev : ev (deriv J s) = phase (deriv J s) x := by
      simp [ev, NecessitySeedJacobian.phaseEvaluation_apply, PaperI.AllDim.phase_three]
    rw [← hev, hv, phase_affineFieldCoefficientMap]
    simp only [J, (hasFDerivAt_phase_affine 4 (upperCenter (g s))
      (upperLinear (g s)) F x).fderiv,
      (hasFDerivAt_phase_affine 4 (upperCenter (g s)) (upperLinear (g s)) F 0).fderiv,
      ContinuousLinearMap.comp_apply, frameLinearMap_apply, Matrix.mulVec_zero, add_zero]
  rwa [← heq]

/-- The differential is an identity of the complete coefficient vector
modulo the discarded constant, in the original moving frame. -/
theorem normalizedQuartic_hasDerivAt
    (F : CoefficientSpace 4) (c d : Plane → ℝ) (y : ℝ → ℝ) (s : ℝ)
    (hc : ContDiffAt ℝ 2 c (characteristicPoint y s))
    (hd : DifferentiableAt ℝ d (characteristicPoint y s))
    (hy : HasDerivAt y (d (characteristicPoint y s)) s)
    (hnull : graphZZ c (characteristicPoint y s) +
        2 * d (characteristicPoint y s) * graphYZ c (characteristicPoint y s) +
        d (characteristicPoint y s)^2 * graphYY c (characteristicPoint y s) = 0) :
    let p := characteristicPoint y s
    let B := mixedCurvature c d p
    let v := nullRate d p
    HasDerivAt (normalizedQuartic F c d y)
      (affineFieldCoefficientMap 4 connectionTranslation (connectionLinear B v)
        (normalizedQuartic F c d y s)) s := by
  dsimp only
  have hframe := tangentFrame_hasDerivAt c d y s hc hd hy hnull
  dsimp only at hframe
  exact upperOrbit_hasDerivAt F _ s _ _ _ _ _ hframe rfl rfl rfl

/-- Each nonconstant coefficient differentiates to the corresponding
ordinary coefficient of (BA+T_z+vD)J. -/
theorem normalizedQuartic_coefficient_hasDerivAt
    (F : CoefficientSpace 4) (c d : Plane → ℝ) (y : ℝ → ℝ) (s : ℝ)
    (hc : ContDiffAt ℝ 2 c (characteristicPoint y s))
    (hd : DifferentiableAt ℝ d (characteristicPoint y s))
    (hy : HasDerivAt y (d (characteristicPoint y s)) s)
    (hnull : graphZZ c (characteristicPoint y s) +
        2 * d (characteristicPoint y s) * graphYZ c (characteristicPoint y s) +
        d (characteristicPoint y s)^2 * graphYY c (characteristicPoint y s) = 0)
    (x₁ x₂ x₃ : ℕ) (h1 : 1 ≤ x₁+x₂+x₃) (h4 : x₁+x₂+x₃ ≤ 4) :
    let p := characteristicPoint y s
    let B := mixedCurvature c d p
    let v := nullRate d p
    let J := fun t => coefficientPolynomial (normalizedQuartic F c d y t)
    HasDerivAt (fun t => coeffAt x₁ x₂ x₃ (J t))
      (coeffAt x₁ x₂ x₃ (nullGenerator B v (J s))) s := by
  dsimp only
  have h := normalizedQuartic_hasDerivAt F c d y s hc hd hy hnull
  dsimp only at h
  let i := index4 x₁ x₂ x₃ h1 h4
  have hd' := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt s h
  let D := affineFieldCoefficientMap 4 connectionTranslation
    (connectionLinear (mixedCurvature c d (characteristicPoint y s))
      (nullRate d (characteristicPoint y s))) (normalizedQuartic F c d y s)
  change HasDerivAt (fun t => normalizedQuartic F c d y t i) (D i) s at hd'
  rw [← coeffAt_coeffSpace D x₁ x₂ x₃ h1 h4, coeffAt] at hd'
  simp_rw [coeffAt_coeffSpace _ x₁ x₂ x₃ h1 h4]
  have hne : exponent x₁ x₂ x₃ ≠ 0 := by
    intro hzero
    have hh := exponent_degree x₁ x₂ x₃
    rw [hzero, Finsupp.degree_zero] at hh
    omega
  unfold D at hd'
  rw [coeff_affineFieldCoefficientMap _ _ _ _ hne,
    nullGenerator_eq_affineFieldPolynomialMap] at hd'
  exact hd'

/-- II2482–II2488. The quotient expression follows wherever the pivot
is nonzero, and the final simplification uses the null slice along the path. -/
theorem quartic_connection_on_characteristic
    (F : CoefficientSpace 4) (c d : Plane → ℝ) (y : ℝ → ℝ) (s : ℝ)
    (hc : ContDiffAt ℝ 2 c (characteristicPoint y s))
    (hd : DifferentiableAt ℝ d (characteristicPoint y s))
    (hy : HasDerivAt y (d (characteristicPoint y s)) s)
    (hnull : graphZZ c (characteristicPoint y s) +
        2 * d (characteristicPoint y s) * graphYZ c (characteristicPoint y s) +
        d (characteristicPoint y s)^2 * graphYY c (characteristicPoint y s) = 0) :
    let p := characteristicPoint y s
    let B := mixedCurvature c d p
    let v := nullRate d p
    let J := fun t => coefficientPolynomial (normalizedQuartic F c d y t)
    let K := nullGenerator B v (J s)
    connectionRow B K = v * connectionPivot B (J s) ∧
    HasDerivAt (fun t => coeffAt 0 1 3 (J t)) (coeffAt 0 1 3 K) s ∧
    HasDerivAt (fun t => coeffAt 1 0 2 (J t)) (coeffAt 1 0 2 K) s ∧
    (connectionPivot B (J s) ≠ 0 →
      v = connectionRow B K / connectionPivot B (J s) ∧
      ((fun t => coeffAt 1 0 2 (J t)) =ᶠ[𝓝 s] 0 →
        v = deriv (fun t => coeffAt 0 1 3 (J t)) s / connectionPivot B (J s))) := by
  dsimp only
  let p := characteristicPoint y s
  let B := mixedCurvature c d p
  let v := nullRate d p
  let J := fun t => coefficientPolynomial (normalizedQuartic F c d y t)
  let K := nullGenerator B v (J s)
  have hrow : connectionRow B K = v * connectionPivot B (J s) :=
    nullGenerator_coeff B v _ (coefficientPolynomial_totalDegree _)
  have hY : HasDerivAt (fun t => coeffAt 0 1 3 (J t)) (coeffAt 0 1 3 K) s :=
    normalizedQuartic_coefficient_hasDerivAt F c d y s hc hd hy hnull 0 1 3 (by decide) (by decide)
  have hX : HasDerivAt (fun t => coeffAt 1 0 2 (J t)) (coeffAt 1 0 2 K) s :=
    normalizedQuartic_coefficient_hasDerivAt F c d y s hc hd hy hnull 1 0 2 (by decide) (by decide)
  refine ⟨hrow,hY,hX,?_⟩
  intro hpivot
  change v = connectionRow B K / connectionPivot B (J s) ∧ _
  refine ⟨(eq_div_iff hpivot).2 hrow.symm, ?_⟩
  intro hslice
  have hz : coeffAt 1 0 2 K = 0 := by
    exact ((hX.congr_of_eventuallyEq hslice.symm).unique (hasDerivAt_const s (0 : ℝ)))
  have hrewrite : connectionRow B K = deriv (fun t => coeffAt 0 1 3 (J t)) s := by
    rw [connectionRow, hz, mul_zero, sub_zero, hY.deriv]
  exact (eq_div_iff hpivot).2 (hrow.symm.trans hrewrite)

/-- The normalized critical graph lifted to ordinary Cartesian coordinates. -/
def graphLift (g : Plane → ℝ) (u : Plane) : PhysicalSpace := ![g u,u.1,u.2]

private theorem graphLift_hasFDerivAt {g : Plane → ℝ} {u : Plane}
    (hg : DifferentiableAt ℝ g u) :
    HasFDerivAt (graphLift g)
      (ContinuousLinearMap.pi ![fderiv ℝ g u, ContinuousLinearMap.fst ℝ ℝ ℝ,
        ContinuousLinearMap.snd ℝ ℝ ℝ]) u := by
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · exact hg.hasFDerivAt
  · exact (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  · exact (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt

private theorem eval_graph_zpartial
    (H : Poly) (g : Plane → ℝ) (u : Plane)
    (hg : DifferentiableAt ℝ g u) :
    graphZ (fun w => eval (graphLift g w) H) u =
      eval (graphLift g u) (pderiv 0 H) * graphZ g u +
      eval (graphLift g u) (pderiv 2 H) := by
  change fderiv ℝ (fun w => eval (graphLift g w) H) u (0,1) = _
  have h := (hasFDerivAt_evalPolynomial H (graphLift g u)).comp u
    (graphLift_hasFDerivAt hg)
  change (fderiv ℝ ((fun z => eval z H) ∘ graphLift g) u) (0,1) = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply, polynomialDifferential_apply]
  simp [Fin.sum_univ_three, graphZ, graphPartial]

/-- The actual normalized graph curvature is the quotient of the two
ordinary coefficient rows. This follows by differentiating its root identity. -/
theorem normalizedGraph_mixed_curvature
    (J : Poly) (g : Plane → ℝ)
    (hg : ContDiffAt ℝ 2 g 0) (hg0 : g 0 = 0) (hDg : fderiv ℝ g 0 = 0)
    (hroot : ∀ᶠ w in 𝓝 (0 : Plane), eval (graphLift g w) (pderiv 0 J) = 0) :
    coeffAt 1 1 1 J + 2 * coeffAt 2 0 0 J * graphYZ g 0 = 0 := by
  let H := pderiv (0 : Fin 3) J
  have hh : (fun w => eval (graphLift g w) H) =ᶠ[𝓝 (0 : Plane)] 0 := hroot
  have hnear : (fun w => eval (graphLift g w) (pderiv 0 H) * graphZ g w +
        eval (graphLift g w) (pderiv 2 H)) =ᶠ[𝓝 (0 : Plane)] 0 := by
    filter_upwards [hh.eventuallyEq_nhds, hg.eventually (by simp)] with w hw hgw
    rw [← eval_graph_zpartial H g w (hgw.differentiableAt (by norm_num))]
    change fderiv ℝ (fun w => eval (graphLift g w) H) w (0,1) = 0
    rw [hw.fderiv_eq]
    simp
  have hl : graphLift g 0 = 0 := by
    ext i
    fin_cases i <;> simp [graphLift, hg0]
  have hD : ∀ P : Poly, HasFDerivAt (fun w => eval (graphLift g w) P)
      ((polynomialDifferential P 0).comp (ContinuousLinearMap.pi
        ![fderiv ℝ g 0, ContinuousLinearMap.fst ℝ ℝ ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ]))
      0 := by
    intro P
    simpa only [hl] using (hasFDerivAt_evalPolynomial P (graphLift g 0)).comp 0
      (graphLift_hasFDerivAt (hg.differentiableAt (by norm_num)))
  have hpartial := (graph_partial_derivative (w := (0,1)) hg).hasFDerivAt
  have hder := ((hD (pderiv 0 H)).mul hpartial).add (hD (pderiv 2 H))
  have hz := (hder.congr_of_eventuallyEq hnear.symm).fderiv
  have he := congrArg (fun L : Plane →L[ℝ] ℝ => L (1,0)) hz
  have hzero : graphZ g 0 = 0 := by simp [graphZ, graphPartial, hDg]
  change (fderiv ℝ (fun _ : Plane => (0 : ℝ)) 0) (1,0) =
    (eval (graphLift g 0) (pderiv 0 H) • fderiv ℝ (graphZ g) 0 + graphZ g 0 •
      (polynomialDifferential (pderiv 0 H) 0).comp
        (ContinuousLinearMap.pi ![fderiv ℝ g 0, ContinuousLinearMap.fst ℝ ℝ ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ]) +
      (polynomialDifferential (pderiv 2 H) 0).comp
        (ContinuousLinearMap.pi ![fderiv ℝ g 0, ContinuousLinearMap.fst ℝ ℝ ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ])) (1,0) at he
  simp only [fderiv_const, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    hzero, zero_mul, add_zero, zero_add, hl, hDg, ContinuousLinearMap.comp_apply] at he
  change 0 = eval 0 (pderiv 0 H) * graphY (graphZ g) 0 +
    polynomialDifferential (pderiv 2 H) 0 ![0,1,0] at he
  rw [graph_mixed_symmetric hg, polynomialDifferential_apply, Fin.sum_univ_three] at he
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.empty_val', mul_zero, mul_one, zero_add, add_zero] at he
  have hx : eval 0 (pderiv 0 H) = 2 * coeffAt 2 0 0 J := by
    rw [eval_zero]
    change coeff 0 (pderiv 0 (pderiv 0 J)) = _
    rw [coeff_polynomialPartial, coeff_polynomialPartial]
    simp [coeffAt, exponent, Finsupp.single_apply, ← Finsupp.single_add]
  have hyz : eval 0 (pderiv 1 (pderiv 2 H)) = coeffAt 1 1 1 J := by
    rw [eval_zero]
    change coeff 0 (pderiv 1 (pderiv 2 (pderiv 0 J))) = _
    rw [coeff_polynomialPartial, coeff_polynomialPartial, coeff_polynomialPartial]
    simp [coeffAt, exponent, Finsupp.single_apply,
      show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
      show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 1 by decide,
      add_comm, add_left_comm, add_assoc]
  rw [hx, hyz] at he
  have htwo : (![0,1,0] : PhysicalSpace) (2 : Fin 3) = 0 := rfl
  rw [htwo, mul_zero, add_zero] at he
  linarith only [he]

private theorem nullModel_rows (a r B Ly Lz L0 : ℝ) :
    coeffAt 2 0 0 (nullModel a r B Ly Lz L0) = a ∧
    coeffAt 1 1 1 (nullModel a r B Ly Lz L0) = -2*a*B ∧
    coeffAt 0 2 2 (nullModel a r B Ly Lz L0) = a*B^2 := by
  rw [nullModel, nullModel_square]
  have hz : (0 : Fin 3 →₀ ℕ) = exponent 0 0 0 := by simp [exponent]
  have h1 : X (1 : Fin 3) = monomial (exponent 0 1 0) (1 : ℝ) := by simp [X, exponent]
  have h2 : X (2 : Fin 3) = monomial (exponent 0 0 1) (1 : ℝ) := by simp [X, exponent]
  rw [h1, h2]
  simp [coeffAt, coeff_add, coeff_C_mul, coeff_monomial, coeff_C, hz, exponent_eq_iff]
  ring

private theorem rationalPivot_stability (m M L K ε a B x z w : ℝ)
    (hm : 0 < m) (hM : 0 < M) (hK : 0 < K)
    (hL : L = 2*M^2+1)
    (hKform : K = 2 + (L+2*M^2)/(3*m) + 4*M^4/(3*m^2))
    (hεK : ε ≤ m^3/K) (ha : m ≤ |a|) (hB : m ≤ |B|)
    (hxlow : m/2 ≤ |x|) (hx : |x-a| ≤ ε) (hz : |z-(-2*a*B)| ≤ ε)
    (hw : |w-a*B^2| ≤ ε)
    (hdiffz : |z^2-(-2*a*B)^2| ≤ ε*(L+2*M^2))
    (hmodelzsq : |(-2*a*B)^2| ≤ 4*M^4) :
    m^3 ≤ |2*w + z^2/(6*x)| := by
  let z₀ := -2*a*B
  let w₀ := a*B^2
  have hxne : x ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) hxlow)
  have hmodel : 2*w₀ + z₀^2/(6*a) = (8/3 : ℝ)*a*B^2 := by
    dsimp [w₀,z₀]
    have hane : a ≠ 0 := abs_pos.mp (hm.trans_le ha)
    field_simp
    ring
  have habsfrac₁ : |(z^2-z₀^2)/(6*x)| ≤ (L+2*M^2)/(3*m)*ε := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    apply (div_le_iff₀ (mul_pos (by norm_num) (abs_pos.mpr hxne))).2
    calc
      |z^2-z₀^2| ≤ ε*(L+2*M^2) := hdiffz
      _ = ((L+2*M^2)/(3*m)*ε)*(3*m) := by field_simp; ring
      _ ≤ ((L+2*M^2)/(3*m)*ε)*(6*|x|) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        exact mul_nonneg (by rw [hL]; positivity) (le_trans (abs_nonneg _) hz)
  have habsfrac₂ : |z₀^2*(a-x)/(6*x*a)| ≤ (4*M^4/(3*m^2))*ε := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6),
      abs_sub_comm a x]
    have hapos : 0 < |a| := hm.trans_le ha
    have hxpos : 0 < |x| := abs_pos.mpr hxne
    apply (div_le_iff₀ (by positivity)).2
    calc
      |z₀^2| * |x-a| ≤ (4*M^4)*ε :=
        mul_le_mul hmodelzsq hx (abs_nonneg _) (by positivity)
      _ = (4*M^4/(3*m^2)*ε)*(3*m^2) := by field_simp
      _ ≤ (4*M^4/(3*m^2)*ε)*(6 * |x| * |a|) := by
        have hden := mul_le_mul (show 3*m ≤ 6*|x| by linarith) ha (le_of_lt hm)
          (by positivity : 0 ≤ 6*|x|)
        apply mul_le_mul_of_nonneg_left (by nlinarith only [hden])
        exact mul_nonneg (by positivity) (le_trans (abs_nonneg _) hz)
  have hsplit : (2*w + z^2/(6*x)) - (2*w₀ + z₀^2/(6*a)) =
      2*(w-w₀) + (z^2-z₀^2)/(6*x) + z₀^2*(a-x)/(6*x*a) := by
    have hane : a ≠ 0 := abs_pos.mp (hm.trans_le ha)
    field_simp
    ring
  have herr : |(2*w + z^2/(6*x)) - (8/3 : ℝ)*a*B^2| ≤ m^3 := by
    rw [← hmodel, hsplit]
    calc
      _ ≤ |2*(w-w₀)| + |(z^2-z₀^2)/(6*x)| + |z₀^2*(a-x)/(6*x*a)| :=
        (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
      _ ≤ K*ε := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        rw [hKform]
        nlinarith only [mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 2), habsfrac₁, habsfrac₂]
      _ ≤ m^3 := by
        calc
          K*ε ≤ K*(m^3/K) := mul_le_mul_of_nonneg_left hεK hK.le
          _ = m^3 := by field_simp
  have hmodelmin : (8/3 : ℝ)*m^3 ≤ |(8/3 : ℝ)*a*B^2| := by
    rw [abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 8/3)]
    have hBsq := mul_le_mul hB hB hm.le (abs_nonneg B)
    have hh := mul_le_mul ha (show m^2 ≤ |B|^2 by simpa only [pow_two] using hBsq)
      (by positivity : 0 ≤ m^2) (abs_nonneg a)
    nlinarith only [hh]
  have htri := abs_add_le (2*w + z^2/(6*x))
    ((8/3 : ℝ)*a*B^2 - (2*w + z^2/(6*x)))
  rw [add_sub_cancel, abs_sub_comm ((8/3 : ℝ)*a*B^2) (2*w + z^2/(6*x))] at htri
  linarith [show 0 ≤ m^3 by positivity]

private theorem uniform_rationalPivot (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (a B x z w : ℝ),
      m ≤ |a| → m ≤ |B| → |a| ≤ M → |B| ≤ M →
      |x-a| ≤ ε → |z-(-2*a*B)| ≤ ε → |w-a*B^2| ≤ ε →
      m^3 ≤ |2*w + z^2/(6*x)| := by
  let L := 2 * M^2 + 1
  let K := 2 + (L + 2*M^2) / (3*m) + 4*M^4 / (3*m^2)
  have hM : 0 < M := hm.trans_le hmM
  have hK : 0 < K := by dsimp [K, L]; positivity
  refine ⟨min 1 (min (m/2) (m^3/K)), by positivity, ?_⟩
  intro a B x z w ha hB haM hBM hx hz hw
  let z₀ := -2*a*B
  let w₀ := a*B^2
  let ε := min 1 (min (m/2) (m^3/K))
  have hεone : ε ≤ 1 := min_le_left _ _
  have hεm : ε ≤ m/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hxa : |a| ≤ |x| + |x-a| := by
    simpa [abs_sub_comm] using abs_add_le x (a-x)
  have hxlow : m/2 ≤ |x| := by linarith
  have hz₀M : |z₀| ≤ 2*M^2 := by
    dsimp [z₀]
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul haM hBM (abs_nonneg B) hM.le]
  have hzbound : |z| ≤ L := by
    have hh := abs_add_le (z-z₀) z₀
    rw [sub_add_cancel] at hh
    dsimp [L]
    linarith
  have hdiffz : |z^2-z₀^2| ≤ ε*(L+2*M^2) := by
    rw [show z^2-z₀^2 = (z-z₀)*(z+z₀) by ring, abs_mul]
    exact mul_le_mul hz ((abs_add_le _ _).trans (add_le_add hzbound hz₀M))
      (abs_nonneg _) (le_trans (abs_nonneg _) hz)
  have hmodelzsq : |z₀^2| ≤ 4*M^4 := by
    rw [abs_pow]
    nlinarith [mul_le_mul hz₀M hz₀M (abs_nonneg z₀) (by positivity : 0 ≤ 2*M^2)]
  exact rationalPivot_stability m M L K ε a B x z w hm hM hK rfl rfl
    ((min_le_right _ _).trans (min_le_right _ _)) ha hB hxlow hx hz hw hdiffz hmodelzsq

/-- The nonzero pivot is uniform in a coefficient neighborhood of all
conditioned compact null models. The pivot is computed with the mixed
curvature of the actual normalized critical graph. -/
theorem nearby_normalizedGraph_connectionPivot (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (a r B Ly Lz L0 : ℝ),
      m ≤ |a| → m ≤ |B| → |a| ≤ M → |B| ≤ M →
      ∀ (J : Poly) (g : Plane → ℝ),
      ContDiffAt ℝ 2 g 0 → g 0 = 0 → fderiv ℝ g 0 = 0 →
      (∀ᶠ w in 𝓝 (0 : Plane), eval (graphLift g w) (pderiv 0 J) = 0) →
      (∀ x y z, 1 ≤ x+y+z → x+y+z ≤ 4 →
        |coeffAt x y z J - coeffAt x y z (nullModel a r B Ly Lz L0)| < ε) →
      m ^ 3 ≤ |connectionPivot (graphYZ g 0) J| := by
  obtain ⟨ε,hε,h⟩ := uniform_rationalPivot m M hm hmM
  refine ⟨min ε (m/2), by positivity, ?_⟩
  intro a r B Ly Lz L0 ha hB haM hBM J g hg hg0 hDg hroot hclose
  let x := coeffAt 2 0 0 J
  let z := coeffAt 1 1 1 J
  let w := coeffAt 0 2 2 J
  obtain ⟨hxM,hzM,hwM⟩ := nullModel_rows a r B Ly Lz L0
  have hx : |x-a| ≤ min ε (m/2) := by
    exact le_of_lt (hxM ▸ hclose 2 0 0 (by decide) (by decide))
  have hz : |z-(-2*a*B)| ≤ ε := by
    have hh := hclose 1 1 1 (by decide) (by decide)
    rw [hzM] at hh
    exact (le_of_lt hh).trans (min_le_left _ _)
  have hw : |w-a*B^2| ≤ ε := by
    have hh := hclose 0 2 2 (by decide) (by decide)
    rw [hwM] at hh
    exact (le_of_lt hh).trans (min_le_left _ _)
  have hxa : |a| ≤ |x| + |x-a| := by
    simpa [abs_sub_comm] using abs_add_le x (a-x)
  have hxlow : m/2 ≤ |x| := by linarith [hx.trans (min_le_right _ _)]
  have hxne : x ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) hxlow)
  have hroot' : z + 2*x*graphYZ g 0 = 0 :=
    normalizedGraph_mixed_curvature J g hg hg0 hDg hroot
  have hBactual : graphYZ g 0 = -z / (2*x) := by
    apply (eq_div_iff (mul_ne_zero two_ne_zero hxne)).2
    linarith only [hroot']
  have hdelta : connectionPivot (graphYZ g 0) J = 2*w + z^2/(6*x) := by
    rw [connectionPivot, hBactual]
    change 2*w - ((-z/(2*x))/3)*z = _
    ring
  rw [hdelta]
  exact h a B x z w ha hB haM hBM (hx.trans (min_le_left _ _)) hz hw

private def shearLinear (d : ℝ) : Plane →L[ℝ] Plane :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ) + d • (ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem shearLinear_apply (d : ℝ) (u : Plane) : shearLinear d u = (u.1+d*u.2,u.2) := rfl

private def tangentBase (d : Plane → ℝ) (p : Plane) (u : Plane) : Plane :=
  p + shearLinear (d p) u

private def tangentOffset (c d : Plane → ℝ) (p : Plane) : Plane →L[ℝ] ℝ :=
  graphY c p • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (graphZ c p + d p * graphY c p) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The same selected critical graph, expressed in the actual moving
normalized tangent frame. -/
def normalizedGraph (c d : Plane → ℝ) (p : Plane) (u : Plane) : ℝ :=
  c (tangentBase d p u) - tangentOffset c d p u - c p

private theorem tangentBase_hasFDerivAt (d : Plane → ℝ) (p u : Plane) :
    HasFDerivAt (tangentBase d p) (shearLinear (d p)) u :=
  (shearLinear (d p)).hasFDerivAt.const_add p

private theorem tangentOffset_eq (c d : Plane → ℝ) (p : Plane) :
    (fderiv ℝ c p).comp (shearLinear (d p)) = tangentOffset c d p := by
  apply ContinuousLinearMap.ext
  intro u
  rcases u with ⟨u,v⟩
  rw [ContinuousLinearMap.comp_apply, shearLinear_apply]
  have he : ((u+d p*v,v) : Plane) = u • ((1,0) : Plane) + v • (d p,1) := by
    ext <;> simp <;> ring
  rw [he, map_add, map_smul, map_smul, direction_decomposition]
  simp [tangentOffset, graphY, graphZ, graphPartial]
  ring

private theorem normalizedGraph_smooth_flat (c d : Plane → ℝ) (p : Plane)
    (hc : ContDiffAt ℝ 2 c p) :
    ContDiffAt ℝ 2 (normalizedGraph c d p) 0 ∧ normalizedGraph c d p 0 = 0 ∧
      fderiv ℝ (normalizedGraph c d p) 0 = 0 := by
  have hbase : tangentBase d p 0 = p := by simp [tangentBase]
  have hcb : ContDiffAt ℝ 2 c (tangentBase d p 0) := by simpa only [hbase] using hc
  have hb : ContDiffAt ℝ 2 (tangentBase d p) 0 :=
    ((contDiff_const (c := p)).add (shearLinear (d p)).contDiff).contDiffAt
  have hcont := ((hcb.comp 0 hb).sub (tangentOffset c d p).contDiff.contDiffAt).sub
    (contDiffAt_const (c := c p))
  refine ⟨hcont, by simp [normalizedGraph, hbase], ?_⟩
  have hc' : DifferentiableAt ℝ c (tangentBase d p 0) :=
    hcb.differentiableAt (by norm_num)
  have h := ((hc'.hasFDerivAt.comp 0 (tangentBase_hasFDerivAt d p 0)).sub
    (tangentOffset c d p).hasFDerivAt).sub (hasFDerivAt_const (c p) (0 : Plane))
  simpa [normalizedGraph, Function.comp_def, hbase, tangentOffset_eq] using h.fderiv

private theorem normalizedGraph_curvature (c d : Plane → ℝ) (p : Plane)
    (hc : ContDiffAt ℝ 2 c p) :
    graphYZ (normalizedGraph c d p) 0 = mixedCurvature c d p := by
  have hbase : tangentBase d p 0 = p := by simp [tangentBase]
  have ht : Tendsto (tangentBase d p) (𝓝 0) (𝓝 p) := by
    simpa only [hbase] using (tangentBase_hasFDerivAt d p 0).continuousAt.tendsto
  have hy : (fun u => graphY (normalizedGraph c d p) u) =ᶠ[𝓝 (0 : Plane)]
      (fun u => graphY c (tangentBase d p u) - graphY c p) := by
    filter_upwards [ht.eventually (hc.eventually (by simp))] with u hcu
    have h := (((hcu.differentiableAt (by norm_num)).hasFDerivAt.comp u
      (tangentBase_hasFDerivAt d p u)).sub (tangentOffset c d p).hasFDerivAt).sub
      (hasFDerivAt_const (c p) u)
    have hgraph : HasFDerivAt (normalizedGraph c d p) _ u := h
    change (fderiv ℝ (normalizedGraph c d p) u) (1,0) = _
    rw [hgraph.fderiv]
    simp [shearLinear_apply, tangentOffset, graphY, graphPartial]
  change fderiv ℝ (fun u => graphY (normalizedGraph c d p) u) 0 (0,1) = _
  rw [hy.fderiv_eq]
  have hcy : DifferentiableAt ℝ (graphY c) (tangentBase d p 0) := by
    rw [hbase]
    exact graph_partial_derivative hc
  have h := (hcy.hasFDerivAt.comp 0 (tangentBase_hasFDerivAt d p 0)).sub
    (hasFDerivAt_const (graphY c p) (0 : Plane))
  have he := congrArg (fun L : Plane →L[ℝ] ℝ => L (0,1)) h.fderiv
  change fderiv ℝ (fun u => graphY c (tangentBase d p u) - graphY c p) 0 (0,1) = _ at he
  rw [he]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply, sub_zero,
    ContinuousLinearMap.comp_apply, shearLinear_apply, hbase, zero_add, mul_one]
  rw [direction_decomposition]
  exact add_comm _ _

private theorem graphLift_normalizedFrame (c d : Plane → ℝ) (p u : Plane) :
    affinePoint (upperCenter (tangentFrame c d p)) (upperLinear (tangentFrame c d p))
      (graphLift (normalizedGraph c d p) u) = graphLift c (tangentBase d p u) := by
  ext i
  fin_cases i <;>
    simp [affinePoint, upperCenter, upperLinear, tangentFrame, graphLift, normalizedGraph,
      tangentBase, tangentOffset, shearLinear_apply, Fin.sum_univ_three, mul_add] <;> ring

private theorem eval_dx_normalized (F : CoefficientSpace 4) (g : Fin 6 → ℝ)
    (x : PhysicalSpace) :
    eval x (pderiv 0 (coefficientPolynomial
      (affineCoefficientMap 4 (upperCenter g) (upperLinear g) F))) =
    eval (affinePoint (upperCenter g) (upperLinear g) x) (pderiv 0 (coefficientPolynomial F)) := by
  let e : PhysicalSpace := Pi.single 0 1
  have he : upperLinear g *ᵥ e = e := by
    ext i
    fin_cases i <;> simp [upperLinear, e, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.single_apply]
  have h := fderiv_phase_affine_apply 4 (upperCenter g) (upperLinear g) F x e
  rw [he] at h
  have hr (J : CoefficientSpace 4) (w : PhysicalSpace) :
      fderiv ℝ (phase J) w e = eval w (pderiv 0 (coefficientPolynomial J)) := by
    simpa [e, eval_coefficientPolynomial] using
      fderiv_evalPolynomial_single (coefficientPolynomial J) w 0
  rw [hr] at h
  simpa [e, Pi.single_apply, Fin.sum_univ_three] using h

private theorem normalizedGraph_isRoot (F : CoefficientSpace 4)
    (c d : Plane → ℝ) (p : Plane)
    (hroot : ∀ᶠ w in 𝓝 p, eval (graphLift c w) (pderiv 0 (coefficientPolynomial F)) = 0) :
    ∀ᶠ u in 𝓝 (0 : Plane), eval (graphLift (normalizedGraph c d p) u)
      (pderiv 0 (coefficientPolynomial (affineCoefficientMap 4
        (upperCenter (tangentFrame c d p)) (upperLinear (tangentFrame c d p)) F))) = 0 := by
  have hbase : tangentBase d p 0 = p := by simp [tangentBase]
  have ht : Tendsto (tangentBase d p) (𝓝 0) (𝓝 p) := by
    simpa only [hbase] using (tangentBase_hasFDerivAt d p 0).continuousAt.tendsto
  filter_upwards [ht.eventually hroot] with u hu
  rw [eval_dx_normalized, graphLift_normalizedFrame]
  exact hu

/-- Uniform quantitative pivot bound in the same moving frame and phase
used by the characteristic endpoint. The graph curvature is derived from
the selected critical graph, not supplied as an independent scalar. -/
theorem normalizedQuartic_uniform_connectionPivot (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (a r B Ly Lz L0 : ℝ),
      m ≤ |a| → m ≤ |B| → |a| ≤ M → |B| ≤ M →
      ∀ (F : CoefficientSpace 4) (c d : Plane → ℝ) (y : ℝ → ℝ) (s : ℝ),
      let p := characteristicPoint y s
      let J := coefficientPolynomial (normalizedQuartic F c d y s)
      ContDiffAt ℝ 2 c p →
      (∀ᶠ w in 𝓝 p, eval (graphLift c w) (pderiv 0 (coefficientPolynomial F)) = 0) →
      (∀ x y z, 1 ≤ x+y+z → x+y+z ≤ 4 →
        |coeffAt x y z J - coeffAt x y z (nullModel a r B Ly Lz L0)| < ε) →
      m^3 ≤ |connectionPivot (mixedCurvature c d p) J| := by
  obtain ⟨ε,hε,h⟩ := nearby_normalizedGraph_connectionPivot m M hm hmM
  refine ⟨ε,hε,?_⟩
  intro a r B Ly Lz L0 ha hB haM hBM F c d y s
  dsimp only
  intro hc hroot hclose
  let p := characteristicPoint y s
  let g := normalizedGraph c d p
  obtain ⟨hgc,hg0,hDg⟩ := normalizedGraph_smooth_flat c d p hc
  have hgr := normalizedGraph_isRoot F c d p hroot
  have hbound := h a r B Ly Lz L0 ha hB haM hBM _ g hgc hg0 hDg hgr hclose
  rw [normalizedGraph_curvature c d p hc] at hbound
  exact hbound

end PaperII.QuarticConnection
