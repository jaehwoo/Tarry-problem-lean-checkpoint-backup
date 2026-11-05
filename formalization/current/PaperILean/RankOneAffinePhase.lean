import PaperILean.StoppedTranslationNonconstant
import PaperILean.AffineNormalPairDegree

/-! I3251: the full scalar-affine factorization and translation-stop contradiction.
The polynomial differential precedes removal of the constant coefficient; the
physical equation retains both its translation and linear parts. -/

noncomputable section
open scoped BigOperators
open Matrix MvPolynomial
namespace PaperI.RankOneAffinePhase

def affineScalar (a : Fin 4 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  C (a (Fin.last 3)) + ∑ j : Fin 3, C (a j.castSucc) * X j

theorem affineScalar_ne_zero (a : Fin 4 → ℝ) (ha : a ≠ 0) :
    affineScalar a ≠ 0 := by
  classical
  intro hz
  apply ha
  have hc : a (Fin.last 3) = 0 := by
    have h := congrArg (MvPolynomial.eval (0 : PhysicalSpace)) hz
    simpa [affineScalar] using h
  have hj (j : Fin 3) : a j.castSucc = 0 := by
    have h := congrArg (MvPolynomial.pderiv j) hz
    have he : C (a j.castSucc) = (0 : MvPolynomial (Fin 3) ℝ) := by
      simpa [affineScalar, MvPolynomial.pderiv_mul, Pi.single_apply, eq_comm] using h
    simpa using congrArg (MvPolynomial.eval (0 : PhysicalSpace)) he
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · exact hc
  · exact hj j

theorem full_phase_factor (b u : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ)
    (a : Fin 4 → ℝ) (hb : ∀ i, b i = u i * a (Fin.last 3))
    (hN : ∀ i j, N i j = u i * a j.castSucc) (F : MvPolynomial (Fin 3) ℝ) :
    affineFieldPolynomialMap b N F = affineScalar a * directionalPolynomialPartial u F := by
  have hcoord (i : Fin 3) : affineCoordinate b N i = C (u i) * affineScalar a := by
    simp only [affineCoordinate, affineScalar, hb, hN, map_mul, mul_add,
      Finset.mul_sum, mul_assoc]
  simp only [affineFieldPolynomialMap_apply, hcoord, directionalPolynomialPartial,
    Finset.mul_sum, MvPolynomial.smul_eq_C_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem physical_factor_annihilated (ell : PhysicalAffineData)
    (b u : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 4 → ℝ)
    (ha : a ≠ 0) (hb : ∀ i, b i = u i * a (Fin.last 3))
    (hN : ∀ i j, N i j = u i * a j.castSucc)
    (hz : physicalAffineFieldAction ell b N = 0) : ell.2 *ᵥ u = 0 := by
  classical
  have ht : ell.2 *ᵥ b = 0 := congrArg Prod.fst hz
  have hl : ell.2 * N = 0 := congrArg Prod.snd hz
  have he (i : Fin 3) (j : Fin 4) : (ell.2 *ᵥ u) i * a j = 0 := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · have h := congrFun ht i
      simpa only [Matrix.mulVec, dotProduct, hb, ← Finset.sum_mul, ← mul_assoc,
        Pi.zero_apply] using h
    · have h := congrFun (congrFun hl i) j
      simpa only [Matrix.mul_apply, hN, ← Finset.sum_mul, ← mul_assoc,
        Matrix.mulVec, dotProduct, Matrix.zero_apply] using h
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra h
    apply ha
    funext j
    simpa using not_exists.mp h j
  funext i
  exact (mul_eq_zero.mp (he i j)).resolve_right hj

theorem raw_stopped_directional_nonconstant {k : ℕ}
    (F : CoefficientSpace k) (ell : PhysicalAffineData) (κ : ℝ) (hκ : 0 < κ)
    (hstop : ∀ u : PhysicalSpace, κ ^ 2 * physicalEuclideanNorm u ^ 2 ≤
      coefficientEuclideanNorm (directionalCoefficientMap k u F) ^ 2 +
        physicalEuclideanNorm (ell.2 *ᵥ u) ^ 2)
    (u : PhysicalSpace) (hu : u ≠ 0) (hBu : ell.2 *ᵥ u = 0) (c : ℝ) :
    directionalPolynomialPartial u (coefficientPolynomial F) ≠ C c := by
  intro hc
  have hz := directionalCoefficientMap_eq_zero_of_constant F u c hc
  have hb := hstop u
  rw [hz, hBu] at hb
  simp only [coefficientEuclideanNorm, physicalEuclideanNorm, coordinateL2Norm,
    Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    Real.sqrt_zero, zero_add] at hb
  have hnorm : physicalEuclideanNorm u = 0 := by
    have hsq : physicalEuclideanNorm u ^ 2 ≤ 0 := by
      apply (mul_le_mul_left (sq_pos_of_pos hκ)).mp
      simpa only [mul_zero] using hb
    nlinarith [physicalEuclideanNorm_nonneg u]
  apply hu
  change coordinateL2Norm u = 0 at hnorm
  rw [coordinateL2Norm_eq_norm, norm_eq_zero] at hnorm
  apply (WithLp.linearEquiv 2 ℝ PhysicalSpace).symm.injective
  simpa only [map_zero] using hnorm

theorem stopped_rankone_action_ne_zero {k : ℕ}
    (F : CoefficientSpace k) (ell : PhysicalAffineData) (κ : ℝ) (hκ : 0 < κ)
    (hstop : ∀ u : PhysicalSpace, κ ^ 2 * physicalEuclideanNorm u ^ 2 ≤
      coefficientEuclideanNorm (directionalCoefficientMap k u F) ^ 2 +
        physicalEuclideanNorm (ell.2 *ᵥ u) ^ 2)
    (b : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ)
    (u : PhysicalSpace) (a : Fin 4 → ℝ) (hu : u ≠ 0) (ha : a ≠ 0)
    (hb : ∀ i, b i = u i * a (Fin.last 3)) (hN : ∀ i j, N i j = u i * a j.castSucc) :
    ¬ (affineFieldCoefficientMap k b N F = 0 ∧ physicalAffineFieldAction ell b N = 0) := by
  rintro ⟨hphase, hphys⟩
  have hBu := physical_factor_annihilated ell b u N a ha hb hN hphys
  have hnc := raw_stopped_directional_nonconstant F ell κ hκ hstop u hu hBu
  have hL := affineScalar_ne_zero a ha
  have hG : directionalPolynomialPartial u (coefficientPolynomial F) ≠ 0 := by
    simpa using hnc 0
  have hdegree : (directionalPolynomialPartial u (coefficientPolynomial F)).totalDegree ≠ 0 := by
    intro hz
    exact hnc _ (totalDegree_eq_zero_iff_eq_C.mp hz)
  have hpoly := polynomial_affineFieldCoefficientMap b N F
  rw [hphase] at hpoly
  have hprod : affineScalar a * directionalPolynomialPartial u (coefficientPolynomial F) =
      C (MvPolynomial.coeff 0 (affineFieldPolynomialMap b N (coefficientPolynomial F))) := by
    rw [← full_phase_factor b u N a hb hN]
    exact sub_eq_zero.mp (by simpa [coefficientPolynomial] using hpoly.symm)
  have hd := polynomial_totalDegree_mul_eq (affineScalar a)
    (directionalPolynomialPartial u (coefficientPolynomial F)) hL hG
  rw [hprod, totalDegree_C] at hd
  omega

end PaperI.RankOneAffinePhase
