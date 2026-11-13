import PaperILean.MixedJetCoefficients

/-! Coordinate Hilbert–Schmidt control for the actual affine jets.

The HS norm is the square root of the sum of squared ordered tensor components
in the standard Euclidean coordinate basis. It is not the operator norm induced
by the PhysicalSpace Pi norm. Only the bounds needed for the fixed coefficient
window are asserted; the two-sided symmetric-tensor coordinate isomorphism and
finite Taylor expansion remain separate obligations.
-/

open scoped BigOperators
open Matrix

noncomputable section
namespace PaperI

theorem monomialExponent_injective (k : ℕ) : Function.Injective (@monomialExponent k) := by
  intro α β h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun e : Fin 3 →₀ ℕ => e i) h

theorem coefficientPolynomial_coeff {k : ℕ} (F : CoefficientSpace k) (α : MonomialIndex k) :
    MvPolynomial.coeff (monomialExponent α) (coefficientPolynomial F) = F α := by
  classical
  rw [coefficientPolynomial_eq_sum, MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial, (monomialExponent_injective k).eq_iff]

theorem abs_le_sqrt_sum_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) (i : ι) :
    |v i| ≤ Real.sqrt (∑ j, (v j) ^ 2) := by
  classical
  calc
    |v i| = Real.sqrt ((v i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, (v j) ^ 2) := Real.sqrt_le_sqrt
      (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

def jetTensorComponent {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) (a : Fin n → Fin 3) : ℝ :=
  iteratedFDeriv ℝ n (phase F) c (fun j => B *ᵥ Pi.single (a j) (1 : ℝ))

def jetTensorHSNorm {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (∑ a : Fin n → Fin 3, (jetTensorComponent F c B n a) ^ 2)

def linearJetEuclideanNorm {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  Real.sqrt (∑ i, (B.transpose *ᵥ phaseCoordinateGradient F c) i ^ 2)

theorem jetTensorHSNorm_nonneg {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) : 0 ≤ jetTensorHSNorm F c B n :=
  Real.sqrt_nonneg _

theorem abs_jetTensorComponent_le_HSNorm {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) (a : Fin n → Fin 3) :
    |jetTensorComponent F c B n a| ≤ jetTensorHSNorm F c B n :=
  abs_le_sqrt_sum_sq _ a

theorem coordinateFactorialProduct_one_le (e : Fin 3 →₀ ℕ) :
    (1 : ℝ) ≤ ((e 2).factorial : ℝ) * ((e 1).factorial : ℝ) * ((e 0).factorial : ℝ) := by
  have h (i : Fin 3) : (1 : ℝ) ≤ ((e i).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (e i))
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (h 2) (h 1)) (h 0)

theorem affineJet_coefficient_le_HSNorm (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k)
    (e : Fin 3 →₀ ℕ) (he : e ≠ 0) :
    |MvPolynomial.coeff e (coefficientPolynomial (affineCoefficientMap k c B F))| ≤
      jetTensorHSNorm F c B (e.sum (fun _ n => n)) := by
  let A : ℝ := ((e 2).factorial : ℝ) * ((e 1).factorial : ℝ) * ((e 0).factorial : ℝ)
  have hA : 1 ≤ A := coordinateFactorialProduct_one_le e
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hcoeff := affineJet_mixed_coefficient k c B F e he
  have hcomponent := abs_jetTensorComponent_le_HSNorm F c B
    (coordinateDerivativeOrder e).length (coordinateDerivativeOrder e).get
  change |iteratedFDeriv ℝ (coordinateDerivativeOrder e).length (phase F) c
      (fun j => B *ᵥ Pi.single ((coordinateDerivativeOrder e).get j) (1 : ℝ))| ≤ _ at hcomponent
  rw [hcoeff, coordinateDerivativeOrder_length] at hcomponent
  change |A * MvPolynomial.coeff e (coefficientPolynomial (affineCoefficientMap k c B F))| ≤ _
    at hcomponent
  rw [abs_mul, abs_of_nonneg hA0] at hcomponent
  have hmul : |MvPolynomial.coeff e (coefficientPolynomial (affineCoefficientMap k c B F))| ≤
      A * |MvPolynomial.coeff e (coefficientPolynomial (affineCoefficientMap k c B F))| := by
    simpa using mul_le_mul_of_nonneg_right hA
      (abs_nonneg (MvPolynomial.coeff e (coefficientPolynomial (affineCoefficientMap k c B F))))
  exact hmul.trans hcomponent

theorem monomialExponent_ne_zero {k : ℕ} (α : MonomialIndex k) : monomialExponent α ≠ 0 := by
  intro h
  have hsum := sum_monomialExponent α
  rw [h] at hsum
  have hp := α.property.1
  simp only [Finsupp.sum_zero_index] at hsum
  omega

theorem affineJet_nonlinear_coefficient_bound (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k) (M : ℝ)
    (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M)
    (α : MonomialIndex k) (hα : 2 ≤ totalDegree α.val) :
    |affineCoefficientMap k c B F α| ≤ M := by
  have h := affineJet_coefficient_le_HSNorm k c B F (monomialExponent α)
    (monomialExponent_ne_zero α)
  rw [coefficientPolynomial_coeff, sum_monomialExponent] at h
  exact h.trans ((Finset.single_le_sum (fun r _ => jetTensorHSNorm_nonneg F c B r)
    (Finset.mem_Icc.mpr ⟨hα, α.property.2⟩)).trans hM)

end PaperI
