import PaperILean.DirectionalCoefficientJets

/-! Actual polynomial derivatives above total degree vanish at every center.
The natural-valued degree of a nonzero constant is zero: the last derivative
is proved zero by differentiating that constant, not by identifying degree
zero with the zero polynomial. No frame invertibility or phase genericity is
assumed. These are prerequisites for retaining the highest directional grade.
-/

noncomputable section
open scoped BigOperators
namespace PaperI

theorem directionalPolynomialPartial_constant (v : PhysicalSpace) (a : ℝ) :
    directionalPolynomialPartial v (MvPolynomial.C a) = 0 := by
  simp [directionalPolynomialPartial]

theorem iteratedDirectionalPolynomialPartial_eq_zero_of_degree_lt (n : ℕ)
    (v : Fin n → PhysicalSpace) (P : MvPolynomial (Fin 3) ℝ)
    (hn : P.totalDegree < n) :
    iteratedDirectionalPolynomialPartial n v P = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    have hdeg := totalDegree_iteratedDirectionalPolynomialPartial_le n (Fin.tail v) P
    have hzero : (iteratedDirectionalPolynomialPartial n (Fin.tail v) P).totalDegree = 0 :=
      by omega
    have hconst := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
    change directionalPolynomialPartial (v 0)
      (iteratedDirectionalPolynomialPartial n (Fin.tail v) P) = 0
    rw [hconst]
    exact directionalPolynomialPartial_constant _ _

theorem iteratedFDeriv_evalPolynomial_eq_zero_of_degree_lt (n : ℕ)
    (P : MvPolynomial (Fin 3) ℝ) (x : PhysicalSpace) (hn : P.totalDegree < n) :
    iteratedFDeriv ℝ n (fun y : PhysicalSpace => MvPolynomial.eval y P) x = 0 := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [iteratedFDeriv_evalPolynomial_directions,
    iteratedDirectionalPolynomialPartial_eq_zero_of_degree_lt n v P hn]
  simp

theorem iteratedFDeriv_phase_eq_zero_of_degree_lt {k : ℕ}
    (F : CoefficientSpace k) (n : ℕ) (x : PhysicalSpace) (hn : k < n) :
    iteratedFDeriv ℝ n (phase F) x = 0 := by
  have hp : (coefficientPolynomial F).totalDegree ≤ k :=
    coefficientPolynomial_totalDegree F
  have heq : phase F = fun y : PhysicalSpace =>
      MvPolynomial.eval y (coefficientPolynomial F) := by
    funext y
    exact (eval_coefficientPolynomial F y).symm
  rw [heq]
  exact iteratedFDeriv_evalPolynomial_eq_zero_of_degree_lt n _ x (hp.trans_lt hn)

theorem affineJetTensor_eq_zero_of_degree_lt {k : ℕ}
    (F : CoefficientSpace k) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (n : ℕ) (hn : k < n) : affineJetTensor F c B n = 0 := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [affineJetTensor_apply, iteratedFDeriv_phase_eq_zero_of_degree_lt F n c hn]
  simp

theorem tensorHSNorm_zero (n : ℕ) : tensorHSNorm (0 : TensorSpace n) = 0 := by
  simp [tensorHSNorm, coordinateL2Norm, tensorCoordinates]

theorem jetTensorHSNorm_eq_zero_of_degree_lt {k : ℕ}
    (F : CoefficientSpace k) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (n : ℕ) (hn : k < n) : jetTensorHSNorm F c B n = 0 := by
  rw [← tensorHSNorm_affineJetTensor,
    affineJetTensor_eq_zero_of_degree_lt F c B n hn, tensorHSNorm_zero]

theorem iteratedFDeriv_affine_directional_top_eq_zero (k : ℕ)
    (F : CoefficientSpace (k + 1)) (c u : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) :
    iteratedFDeriv ℝ (k + 1)
      (phase (directionalCoefficientMap (k + 1) u
        (affineCoefficientMap (k + 1) c B F))) 0 = 0 := by
  rw [iteratedFDeriv_affine_directional_positive,
    affineJetTensor_eq_zero_of_degree_lt F c B (k + 2) (by omega)]
  apply ContinuousMultilinearMap.ext
  intro v
  simp

end PaperI
