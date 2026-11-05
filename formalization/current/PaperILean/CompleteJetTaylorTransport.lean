import PaperILean.PolynomialLineTaylor
import PaperILean.AffineJetDerivatives

/-! Finite Taylor reconstruction and exact center transport, Paper I 161–176.
The tensor transport equality is pointwise on arbitrary slots. Contractions
prepend displacement slots; the checked symmetry theorem makes their choice
of position immaterial. No inverse frame, phase-dependent frame choice or
uniformity loss is introduced.
-/

open scoped BigOperators
open Matrix
noncomputable section
namespace PaperI

theorem evalPolynomial_finite_taylor_nonconstant (P : MvPolynomial (Fin 3) ℝ)
    (k : ℕ) (hP : P.totalDegree ≤ k) (c v : PhysicalSpace) :
    MvPolynomial.eval (c + v) P - MvPolynomial.eval c P =
      ∑ n ∈ Finset.range k, ((n + 1).factorial : ℝ)⁻¹ *
        iteratedFDeriv ℝ (n + 1) (fun x : PhysicalSpace => MvPolynomial.eval x P) c
          (fun _ => v) := by
  have ht := evalPolynomial_finite_taylor P k hP c v
  rw [Finset.sum_range_succ'] at ht
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
    iteratedFDeriv_zero_apply] at ht
  linarith

theorem phase_finite_taylor {k : ℕ} (F : CoefficientSpace k) (c v : PhysicalSpace) :
    phase F (c + v) - phase F c = ∑ n ∈ Finset.range k,
      ((n + 1).factorial : ℝ)⁻¹ * iteratedFDeriv ℝ (n + 1) (phase F) c (fun _ => v) := by
  simpa only [eval_coefficientPolynomial] using
    evalPolynomial_finite_taylor_nonconstant (coefficientPolynomial F) k
      (coefficientPolynomial_totalDegree F) c v

theorem phase_affine_finite_taylor (k : ℕ) (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) :
    phase (affineCoefficientMap k c B F) u = ∑ n ∈ Finset.range k,
      ((n + 1).factorial : ℝ)⁻¹ *
        iteratedFDeriv ℝ (n + 1) (phase F) c (fun _ => B *ᵥ u) := by
  rw [phase_affineCoefficientMap]
  exact phase_finite_taylor F c (B *ᵥ u)

theorem evalPolynomial_derivative_center_transport (P : MvPolynomial (Fin 3) ℝ)
    (k : ℕ) (hP : P.totalDegree ≤ k) (r : ℕ)
    (c h : PhysicalSpace) (v : Fin r → PhysicalSpace) :
    iteratedFDeriv ℝ r (fun x : PhysicalSpace => MvPolynomial.eval x P) (c + h) v =
      ∑ m ∈ Finset.range (k - r + 1), (m.factorial : ℝ)⁻¹ *
        iteratedFDeriv ℝ (r + m) (fun x : PhysicalSpace => MvPolynomial.eval x P) c
          (prependDirections m r (fun _ => h) v) := by
  have hd : (iteratedDirectionalPolynomialPartial r v P).totalDegree ≤ k - r :=
    (totalDegree_iteratedDirectionalPolynomialPartial_le r v P).trans
      (Nat.sub_le_sub_right hP r)
  have ht := evalPolynomial_finite_taylor (iteratedDirectionalPolynomialPartial r v P)
    (k - r) hd c h
  rw [iteratedFDeriv_evalPolynomial_directions]
  rw [ht]
  apply Finset.sum_congr rfl
  intro m hm
  rw [iteratedFDeriv_evalPolynomial_directions,
    iteratedFDeriv_evalPolynomial_directions,
    iteratedDirectionalPolynomialPartial_prepend]

theorem phase_derivative_center_transport {k : ℕ} (F : CoefficientSpace k)
    (r : ℕ) (c h : PhysicalSpace) (v : Fin r → PhysicalSpace) :
    iteratedFDeriv ℝ r (phase F) (c + h) v =
      ∑ m ∈ Finset.range (k - r + 1), (m.factorial : ℝ)⁻¹ *
        iteratedFDeriv ℝ (r + m) (phase F) c (prependDirections m r (fun _ => h) v) := by
  simpa only [eval_coefficientPolynomial] using
    evalPolynomial_derivative_center_transport (coefficientPolynomial F) k
      (coefficientPolynomial_totalDegree F) r c h v

theorem affineJet_center_transport (k : ℕ) (F : CoefficientSpace k)
    (r : ℕ) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (h : PhysicalSpace) (v : Fin r → PhysicalSpace) :
    iteratedFDeriv ℝ r (phase F) (c + B *ᵥ h) (fun j => B *ᵥ v j) =
      ∑ m ∈ Finset.range (k - r + 1), (m.factorial : ℝ)⁻¹ *
        iteratedFDeriv ℝ (r + m) (phase F) c
          (prependDirections m r (fun _ => B *ᵥ h) (fun j => B *ᵥ v j)) :=
  phase_derivative_center_transport F r c (B *ᵥ h) (fun j => B *ᵥ v j)

theorem affineJet_right_frame_change (k : ℕ) (F : CoefficientSpace k)
    (r : ℕ) (c : PhysicalSpace) (B A : Matrix (Fin 3) (Fin 3) ℝ)
    (v : Fin r → PhysicalSpace) :
    iteratedFDeriv ℝ r (phase F) c (fun j => (B * A) *ᵥ v j) =
      iteratedFDeriv ℝ r (phase F) c (fun j => B *ᵥ (A *ᵥ v j)) := by
  simp only [Matrix.mulVec_mulVec]

theorem affineJet_linear_diagonal (k : ℕ) (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) :
    iteratedFDeriv ℝ 1 (phase F) c (fun _ => B *ᵥ u) =
      ∑ i, (B.transpose *ᵥ phaseCoordinateGradient F c) i * u i := by
  rw [← iteratedFDeriv_phase_affine_zero_positive k c B F 0 (fun _ => u),
    iteratedFDeriv_one_apply, (hasFDerivAt_phase (affineCoefficientMap k c B F) 0).fderiv,
    polynomialDifferential_apply]
  change (∑ i, phaseCoordinateGradient (affineCoefficientMap k c B F) 0 i * u i) = _
  rw [phaseCoordinateGradient_affine]

theorem phase_affine_complete_jet (k : ℕ) (hk : 1 ≤ k) (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) :
    phase (affineCoefficientMap k c B F) u =
      (∑ i, (B.transpose *ᵥ phaseCoordinateGradient F c) i * u i) +
      ∑ n ∈ Finset.range (k - 1), ((n + 2).factorial : ℝ)⁻¹ *
        iteratedFDeriv ℝ (n + 2) (phase F) c (fun _ => B *ᵥ u) := by
  cases k with
  | zero => omega
  | succ k =>
      have ht := phase_affine_finite_taylor (k + 1) F c B u
      rw [Finset.sum_range_succ'] at ht
      simp only [Nat.zero_add, Nat.factorial_one, Nat.cast_one, inv_one, one_mul] at ht
      change phase (affineCoefficientMap (k + 1) c B F) u =
        (∑ n ∈ Finset.range k, ((n + 2).factorial : ℝ)⁻¹ *
          iteratedFDeriv ℝ (n + 2) (phase F) c (fun _ => B *ᵥ u)) +
        iteratedFDeriv ℝ 1 (phase F) c (fun _ => B *ᵥ u) at ht
      rw [affineJet_linear_diagonal] at ht
      simpa only [Nat.add_sub_cancel, add_comm] using ht

end PaperI
