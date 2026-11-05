import PaperILean.CompleteSymmetricJetEquiv
import PaperILean.BoundedJetCenterVariation

/-! The actual directional derivative class in the manuscript's full coefficient
space. Only its constant is discarded. Positive jets are the actual contracted
derivatives, at arbitrary orders and centers; no stopping bound is assumed.
-/

noncomputable section
open scoped BigOperators
namespace PaperI

def directionalPolynomialMap (u : PhysicalSpace) :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, u i • (MvPolynomial.pderiv i).toLinearMap

theorem directionalPolynomialMap_apply (u : PhysicalSpace)
    (P : MvPolynomial (Fin 3) ℝ) :
    directionalPolynomialMap u P = directionalPolynomialPartial u P := by
  simp [directionalPolynomialMap, directionalPolynomialPartial]

def directionalBoundedMap (k : ℕ) (u : PhysicalSpace) :
    BoundedPolynomialSpace k →ₗ[ℝ] BoundedPolynomialSpace k where
  toFun P := ⟨directionalPolynomialMap u P.val,
    (MvPolynomial.mem_restrictTotalDegree (Fin 3) k _).mpr
      (by rw [directionalPolynomialMap_apply]
          exact (totalDegree_directionalPolynomialPartial_le u P.val).trans
            ((Nat.sub_le _ _).trans
              ((MvPolynomial.mem_restrictTotalDegree (Fin 3) k P.val).mp P.property)))⟩
  map_add' P Q := Subtype.ext ((directionalPolynomialMap u).map_add P.val Q.val)
  map_smul' a P := Subtype.ext ((directionalPolynomialMap u).map_smul a P.val)

def directionalCoefficientMap (k : ℕ) (u : PhysicalSpace) :
    CoefficientSpace k →ₗ[ℝ] CoefficientSpace k :=
  (coefficientPolynomialEquiv k).symm.toLinearMap.comp
    ((discardConstant k).comp ((directionalBoundedMap k u).comp (coefficientToBounded k)))

theorem polynomial_directionalCoefficientMap {k : ℕ} (u : PhysicalSpace)
    (F : CoefficientSpace k) :
    coefficientPolynomial (directionalCoefficientMap k u F) =
      directionalPolynomialPartial u (coefficientPolynomial F) -
        MvPolynomial.C (MvPolynomial.coeff 0
          (directionalPolynomialPartial u (coefficientPolynomial F))) := by
  change ((coefficientPolynomialEquiv k)
    ((coefficientPolynomialEquiv k).symm
      (discardConstant k (directionalBoundedMap k u (coefficientToBounded k F))))).val = _
  rw [LinearEquiv.apply_symm_apply, discardConstant_eq]
  change directionalPolynomialMap u (coefficientPolynomial F) -
    MvPolynomial.C (MvPolynomial.coeff 0
      (directionalPolynomialMap u (coefficientPolynomial F))) = _
  rw [directionalPolynomialMap_apply]

theorem phase_directionalCoefficientMap {k : ℕ} (u : PhysicalSpace)
    (F : CoefficientSpace k) (x : PhysicalSpace) :
    phase (directionalCoefficientMap k u F) x =
      fderiv ℝ (phase F) x u - fderiv ℝ (phase F) 0 u := by
  rw [← eval_coefficientPolynomial, polynomial_directionalCoefficientMap]
  simp only [map_sub, MvPolynomial.eval_C]
  change MvPolynomial.eval x (directionalPolynomialPartial u (coefficientPolynomial F)) -
    MvPolynomial.constantCoeff (directionalPolynomialPartial u (coefficientPolynomial F)) = _
  rw [← MvPolynomial.eval_zero, eval_directionalPolynomialPartial,
    eval_directionalPolynomialPartial]
  simp only [eval_coefficientPolynomial]

theorem coeff_directionalPolynomialPartial (u : PhysicalSpace)
    (P : MvPolynomial (Fin 3) ℝ) (e : Fin 3 →₀ ℕ) :
    MvPolynomial.coeff e (directionalPolynomialPartial u P) =
      ∑ i : Fin 3, u i * ((e i + 1 : ℕ) : ℝ) *
        MvPolynomial.coeff (e + Finsupp.single i 1) P := by
  simp [directionalPolynomialPartial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, coeff_polynomialPartial, smul_eq_mul, mul_assoc]

theorem coeff_directionalCoefficientMap {k : ℕ} (u : PhysicalSpace)
    (F : CoefficientSpace k) (e : Fin 3 →₀ ℕ) (he : e ≠ 0) :
    MvPolynomial.coeff e (coefficientPolynomial (directionalCoefficientMap k u F)) =
      ∑ i : Fin 3, u i * ((e i + 1 : ℕ) : ℝ) *
        MvPolynomial.coeff (e + Finsupp.single i 1) (coefficientPolynomial F) := by
  rw [polynomial_directionalCoefficientMap, MvPolynomial.coeff_sub]
  simp only [MvPolynomial.coeff_C, if_neg (Ne.symm he), sub_zero]
  exact coeff_directionalPolynomialPartial u _ e

theorem polynomialPartial_commute (i j : Fin 3) (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  apply MvPolynomial.ext
  intro e
  rw [coeff_polynomialPartial, coeff_polynomialPartial,
    coeff_polynomialPartial, coeff_polynomialPartial]
  by_cases hij : i = j
  · subst j
    rfl
  · have hshift : e + Finsupp.single i 1 + Finsupp.single j 1 =
        e + Finsupp.single j 1 + Finsupp.single i 1 := by ac_rfl
    rw [hshift]
    simp only [Finsupp.add_apply, Finsupp.single_apply,
      if_neg hij, if_neg (Ne.symm hij), add_zero]
    ring

theorem directionalPolynomialPartial_commute (u v : PhysicalSpace)
    (P : MvPolynomial (Fin 3) ℝ) :
    directionalPolynomialPartial u (directionalPolynomialPartial v P) =
      directionalPolynomialPartial v (directionalPolynomialPartial u P) := by
  classical
  simp only [directionalPolynomialPartial, map_sum, map_smul, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Derivation.map_smul, smul_smul]
  rw [polynomialPartial_commute, mul_comm]

theorem iteratedDirectionalPolynomialPartial_directional (n : ℕ)
    (v : Fin n → PhysicalSpace) (u : PhysicalSpace) (P : MvPolynomial (Fin 3) ℝ) :
    iteratedDirectionalPolynomialPartial n v (directionalPolynomialPartial u P) =
      directionalPolynomialPartial u (iteratedDirectionalPolynomialPartial n v P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDirectionalPolynomialPartial, ih,
      directionalPolynomialPartial_commute]
    rfl

theorem iteratedFDeriv_directionalPolynomial (n : ℕ) (u x : PhysicalSpace)
    (P : MvPolynomial (Fin 3) ℝ) (v : Fin n → PhysicalSpace) :
    iteratedFDeriv ℝ n (fun y : PhysicalSpace =>
      MvPolynomial.eval y (directionalPolynomialPartial u P)) x v =
        iteratedFDeriv ℝ (n + 1) (fun y : PhysicalSpace => MvPolynomial.eval y P) x
          (Fin.cons u v) := by
  rw [iteratedFDeriv_evalPolynomial_directions,
    iteratedFDeriv_evalPolynomial_directions,
    iteratedDirectionalPolynomialPartial_directional]
  simp [iteratedDirectionalPolynomialPartial]

theorem iteratedFDeriv_directionalCoefficient_positive {k : ℕ}
    (F : CoefficientSpace k) (u x : PhysicalSpace) (n : ℕ) :
    iteratedFDeriv ℝ (n + 1) (phase (directionalCoefficientMap k u F)) x =
      (iteratedFDeriv ℝ (n + 2) (phase F) x).curryLeft u := by
  have heq : phase (directionalCoefficientMap k u F) =
      fun y : PhysicalSpace => MvPolynomial.eval y
        (directionalPolynomialPartial u (coefficientPolynomial F)) +
          (-MvPolynomial.coeff 0
            (directionalPolynomialPartial u (coefficientPolynomial F))) := by
    funext y
    rw [← eval_coefficientPolynomial, polynomial_directionalCoefficientMap]
    simp [sub_eq_add_neg]
  rw [heq, iteratedFDeriv_add_apply' (i := n + 1)
    (contDiff_evalPolynomial _ _).contDiffAt contDiffAt_const]
  simp only [iteratedFDeriv_succ_const, Pi.zero_apply, add_zero]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.curryLeft_apply]
  simpa only [eval_coefficientPolynomial] using
    iteratedFDeriv_directionalPolynomial (n + 1) u x (coefficientPolynomial F) v

theorem iteratedFDeriv_affine_directional_positive {k : ℕ}
    (F : CoefficientSpace k) (c u : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) :
    iteratedFDeriv ℝ (n + 1)
      (phase (directionalCoefficientMap k u (affineCoefficientMap k c B F))) 0 =
        (affineJetTensor F c B (n + 2)).curryLeft u := by
  rw [iteratedFDeriv_directionalCoefficient_positive,
    iteratedFDeriv_phase_affine_positive, affinePoint_zero]
  rfl

end PaperI
