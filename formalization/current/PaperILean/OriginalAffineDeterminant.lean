import PaperILean.AllDimAffineCharacterTargets
import PaperILean.OriginalOrthogonalCharacter
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.StarOrdered

/-! Original proof of Lemma 2.1(i): translation triangularity, homogeneous
permutation symmetry and hockey-stick, orthogonal pullback, and all-rank SVD.
The coefficient quotient is unchanged. No alternative general affine
determinant formula or all-degree marked-exponent count is used. -/

open scoped BigOperators Matrix
noncomputable section
namespace PaperI.AllDim.Original

local instance (n k : ℕ) : DecidableEq (MonomialIndex n k) := Classical.decEq _

/-- The full homogeneous degree `r` monomial index, including `r = 0`. -/
def HomogeneousIndex (n r : ℕ) := {α : Fin n → ℕ // ∑ i, α i = r}

instance (n r : ℕ) : Fintype (HomogeneousIndex n r) :=
  Fintype.ofEquiv (Sym (Fin n) r) (Sym.equivNatSumOfFintype (Fin n) r)

def homogeneousPermutationEquiv (n r : ℕ) (e : Fin n ≃ Fin n) :
    HomogeneousIndex n r ≃ HomogeneousIndex n r where
  toFun α := ⟨fun i => α.val (e i), (e.sum_comp α.val).trans α.property⟩
  invFun α := ⟨fun i => α.val (e.symm i), (e.symm.sum_comp α.val).trans α.property⟩
  left_inv α := by apply Subtype.ext; funext i; simp
  right_inv α := by apply Subtype.ext; funext i; simp

/-- The manuscript's permutation symmetry, before the double count. -/
theorem homogeneous_coordinate_symmetry (n r : ℕ) (i j : Fin n) :
    (∑ α : HomogeneousIndex n r, α.val i) =
      ∑ α : HomogeneousIndex n r, α.val j := by
  have h := (homogeneousPermutationEquiv n r (Equiv.swap i j)).sum_comp
    (fun α : HomogeneousIndex n r => α.val i)
  simpa only [homogeneousPermutationEquiv, Equiv.coe_fn_mk, Equiv.swap_apply_left] using h.symm

/-- Double counting the exponent sum gives `n` times any one coordinate. -/
theorem homogeneous_coordinate_double_count (n r : ℕ) (i : Fin n) :
    n * (∑ α : HomogeneousIndex n r, α.val i) =
      r * Fintype.card (HomogeneousIndex n r) := by
  calc
    n * (∑ α : HomogeneousIndex n r, α.val i) =
        ∑ j : Fin n, ∑ α : HomogeneousIndex n r, α.val i := by simp
    _ = ∑ j : Fin n, ∑ α : HomogeneousIndex n r, α.val j := by
      apply Finset.sum_congr rfl
      intro j _
      exact homogeneous_coordinate_symmetry n r i j
    _ = ∑ α : HomogeneousIndex n r, ∑ j : Fin n, α.val j := Finset.sum_comm
    _ = r * Fintype.card (HomogeneousIndex n r) := by
      have hα (α : HomogeneousIndex n r) : (∑ j : Fin n, α.val j) = r := α.property
      simp only [hα, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      exact Nat.mul_comm _ _

theorem card_homogeneousIndex (d r : ℕ) :
    Fintype.card (HomogeneousIndex (d + 1) r) = (r + d).choose d := by
  let e : HomogeneousIndex (d + 1) r ≃ Sym (Fin (d + 1)) r :=
    (Sym.equivNatSumOfFintype (Fin (d + 1)) r).symm
  rw [Fintype.card_congr e, Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have h : d + 1 + r - 1 = r + d := by omega
  rw [h]
  exact Nat.choose_symm_of_eq_add (by omega)

/-- The binomial simplification in the displayed homogeneous exponent. -/
theorem homogeneous_binomial_balance (d r : ℕ) :
    r * (r + d).choose d = (d + 1) * (r + d).choose (d + 1) := by
  have h := Nat.succ_mul_choose_eq (r + d) d
  rw [Nat.choose_succ_succ] at h
  simp only [Nat.succ_eq_add_one] at h
  nlinarith

/-- The degree-`r` exponent, obtained by symmetry and double counting. -/
theorem homogeneous_coordinate_exponent (d r : ℕ) (i : Fin (d + 1)) :
    (∑ α : HomogeneousIndex (d + 1) r, α.val i) = (r + d).choose (d + 1) := by
  have h := homogeneous_coordinate_double_count (d + 1) r i
  rw [card_homogeneousIndex, homogeneous_binomial_balance] at h
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < d + 1) h

/-- The displayed hockey-stick identity, with `r = j + 1`. -/
theorem homogeneous_exponent_hockeyStick (d k : ℕ) :
    (∑ j ∈ Finset.range k, (j + 1 + d).choose (d + 1)) =
      (k + d + 1).choose (d + 2) := by
  cases k with
  | zero => simp [Nat.choose_eq_zero_of_lt (by omega : d + 1 < d + 2)]
  | succ k =>
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Nat.sum_range_add_choose k (d + 1)

/-- Original homogeneous diagonal action, without excluding zero eigenvalues. -/
def homogeneousDiagonalMap (n r : ℕ) (b : Fin n → ℝ) :
    (HomogeneousIndex n r → ℝ) →ₗ[ℝ] (HomogeneousIndex n r → ℝ) :=
  LinearMap.pi (fun α : HomogeneousIndex n r =>
    (LinearMap.mulLeft ℝ (∏ i, b i ^ α.val i)).comp (LinearMap.proj α))

theorem homogeneousDiagonalMap_det (d r : ℕ) (b : Fin (d + 1) → ℝ) :
    LinearMap.det (homogeneousDiagonalMap (d + 1) r b) =
      (∏ i, b i) ^ (r + d).choose (d + 1) := by
  classical
  rw [homogeneousDiagonalMap, LinearMap.det_pi]
  simp_rw [LinearMap.det_mulLeft]
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum, homogeneous_coordinate_exponent]
  rw [Finset.prod_pow]

/-- Product over positive homogeneous degrees: the manuscript's exponent. -/
theorem homogeneousDiagonalMap_det_product (d k : ℕ) (b : Fin (d + 1) → ℝ) :
    (∏ j ∈ Finset.range k, LinearMap.det (homogeneousDiagonalMap (d + 1) (j + 1) b)) =
      (∏ i, b i) ^ chi (d + 1) k := by
  simp_rw [homogeneousDiagonalMap_det]
  rw [Finset.prod_pow_eq_pow_sum, homogeneous_exponent_hockeyStick]
  simp only [chi, Nat.add_assoc]

/-- The original grading as a disjoint union of positive homogeneous degrees. -/
def homogeneousCompleteMap (n k : ℕ) :
    (Σ r : Fin k, HomogeneousIndex n (r.val + 1)) → MonomialIndex n k :=
  fun z => ⟨fun i => ⟨z.2.val i, Nat.lt_succ_of_le
    ((naturalExponent_le_sum z.2.val i).trans (z.2.property.le.trans (by omega)))⟩,
    by change 1 ≤ ∑ i, z.2.val i ∧ (∑ i, z.2.val i) ≤ k
       rw [z.2.property]
       constructor <;> omega⟩

theorem homogeneousCompleteMap_bijective (n k : ℕ) :
    Function.Bijective (homogeneousCompleteMap n k) := by
  constructor
  · rintro ⟨r, α⟩ ⟨s, β⟩ h
    have hαβ : α.val = β.val := by
      funext i
      exact congrArg (fun z : MonomialIndex n k => (z.val i).val) h
    have hrs : r = s := by
      apply Fin.ext
      have he : r.val + 1 = s.val + 1 := α.property.symm.trans
        ((congrArg (fun f : Fin n → ℕ => ∑ i, f i) hαβ).trans β.property)
      omega
    subst s
    have hab : α = β := Subtype.ext hαβ
    subst β
    rfl
  · intro α
    let r : Fin k := ⟨totalDegree α.val - 1, by have h := α.property; omega⟩
    have hr : totalDegree α.val = r.val + 1 := by
      dsimp [r]
      have h := α.property.1
      omega
    refine ⟨⟨r, ⟨fun i => (α.val i).val, hr⟩⟩, ?_⟩
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl

def homogeneousCompleteEquiv (n k : ℕ) :
    (Σ r : Fin k, HomogeneousIndex n (r.val + 1)) ≃ MonomialIndex n k :=
  Equiv.ofBijective (homogeneousCompleteMap n k) (homogeneousCompleteMap_bijective n k)

/-- The complete exponent sum, now proved using the original grading. -/
theorem sum_monomialCoordinate_original (d k : ℕ) (i : Fin (d + 1)) :
    (∑ α : MonomialIndex (d + 1) k, (α.val i).val) = chi (d + 1) k := by
  have h := (homogeneousCompleteEquiv (d + 1) k).sum_comp
    (fun α : MonomialIndex (d + 1) k => (α.val i).val)
  change (∑ z : (Σ r : Fin k, HomogeneousIndex (d + 1) (r.val + 1)), z.2.val i) = _ at h
  rw [← h, Fintype.sum_sigma]
  simp_rw [homogeneous_coordinate_exponent]
  change (∑ x : Fin k, (fun j : ℕ => (j + 1 + d).choose (d + 1)) x.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (j + 1 + d).choose (d + 1)) k,
    homogeneous_exponent_hockeyStick]
  simp only [chi, Nat.add_assoc]

/-- The actual coefficient map, using the original homogeneous exponent proof. -/
theorem affineCoefficientMap_diagonal_det_original (d k : ℕ) (b : Fin (d + 1) → ℝ) :
    LinearMap.det (affineCoefficientMap (d + 1) k 0 (Matrix.diagonal b)) =
      (∏ i, b i) ^ chi (d + 1) k := by
  classical
  rw [affineCoefficientMap_diagonal, diagonalCoefficientMap, LinearMap.det_pi]
  simp_rw [LinearMap.det_mulLeft]
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum, sum_monomialCoordinate_original]
  rw [Finset.prod_pow]

theorem monomialExponent_injective (n k : ℕ) :
    Function.Injective (@monomialExponent n k) := by
  intro α β h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun e : Fin n →₀ ℕ => e i) h

theorem coefficientPolynomial_coeff {n k : ℕ} (F : CoefficientSpace n k)
    (α : MonomialIndex n k) :
    MvPolynomial.coeff (monomialExponent α) (coefficientPolynomial F) = F α := by
  classical
  rw [coefficientPolynomial_eq_sum, MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial, (monomialExponent_injective n k).eq_iff]

theorem coefficientPolynomial_single {n k : ℕ} (α : MonomialIndex n k) :
    coefficientPolynomial (Pi.single α (1 : ℝ)) =
      MvPolynomial.monomial (monomialExponent α) (1 : ℝ) := by
  classical
  rw [coefficientPolynomial_eq_sum]
  simp only [Pi.single_apply]
  simp_rw [apply_ite]
  simp

theorem monomialExponent_ne_zero {n k : ℕ} (α : MonomialIndex n k) :
    monomialExponent α ≠ 0 := by
  intro h
  have hs := sum_monomialExponent α
  rw [h] at hs
  have hp := α.property.1
  simp only [Finsupp.sum_zero_index] at hs
  omega

theorem affineCoordinate_translation {n : ℕ} (c : PhysicalSpace n) (i : Fin n) :
    affineCoordinate c (1 : Matrix (Fin n) (Fin n) ℝ) i =
      MvPolynomial.X i + MvPolynomial.C (c i) := by
  classical
  simp [affineCoordinate, Matrix.one_apply, eq_comm, add_comm]

/-- The translated monomial before the quotient removes its constant. -/
def translatedMonomial {n k : ℕ} (c : PhysicalSpace n) (α : MonomialIndex n k) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i, (MvPolynomial.X i + MvPolynomial.C (c i)) ^ (α.val i).val

theorem affinePolynomialMap_single {n k : ℕ} (c : PhysicalSpace n)
    (α : MonomialIndex n k) :
    affinePolynomialMap c 1 (coefficientPolynomial (Pi.single α (1 : ℝ))) =
      translatedMonomial c α := by
  classical
  rw [coefficientPolynomial_single]
  unfold affinePolynomialMap translatedMonomial
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype]
  · simp only [map_one, one_mul, affineCoordinate_translation, monomialExponent_apply]
  · intro i
    simp

/-- Constants removed by the quotient do not affect any matrix entry. -/
theorem translation_matrix_entry {n k : ℕ} (c : PhysicalSpace n)
    (α β : MonomialIndex n k) :
    affineCoefficientMap n k c 1 (Pi.single β 1) α =
      MvPolynomial.coeff (monomialExponent α) (translatedMonomial c β) := by
  rw [← coefficientPolynomial_coeff (affineCoefficientMap n k c 1 (Pi.single β 1)) α,
    polynomial_affineCoefficientMap,
    MvPolynomial.coeff_sub, affinePolynomialMap_single, MvPolynomial.coeff_C,
    if_neg (Ne.symm (monomialExponent_ne_zero α)), sub_zero]

/-- Translation cannot increase a column's total degree. -/
theorem translation_matrix_degree_triangular {n k : ℕ} (c : PhysicalSpace n)
    (α β : MonomialIndex n k) (h : totalDegree β.val < totalDegree α.val) :
    affineCoefficientMap n k c 1 (Pi.single β 1) α = 0 := by
  rw [translation_matrix_entry]
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  change (translatedMonomial c β).totalDegree < (monomialExponent α).sum (fun _ e => e)
  rw [sum_monomialExponent, ← affinePolynomialMap_single]
  apply lt_of_le_of_lt (affinePolynomialMap_degree c 1 _) _
  rw [coefficientPolynomial_single, MvPolynomial.totalDegree_monomial (monomialExponent β) (by norm_num),
    sum_monomialExponent]
  exact h

theorem translatedMonomial_monic {n k : ℕ} (m : MonomialOrder (Fin n))
    (c : PhysicalSpace n) (α : MonomialIndex n k) :
    m.Monic (translatedMonomial c α) := by
  apply MonomialOrder.Monic.prod
  intro i _
  exact (m.monic_X_add_C i (c i)).pow

theorem translatedMonomial_degree {n k : ℕ} (m : MonomialOrder (Fin n))
    (c : PhysicalSpace n) (α : MonomialIndex n k) :
    m.degree (translatedMonomial c α) = monomialExponent α := by
  unfold translatedMonomial
  rw [MonomialOrder.degree_prod]
  · simp_rw [MonomialOrder.degree_pow, MonomialOrder.degree_X_add_C]
    ext j
    simp [Finsupp.single_apply]
  · intro i _
    exact pow_ne_zero _ (m.monic_X_add_C i (c i)).ne_zero

/-- The diagonal entries are one, independently of the center. -/
theorem translation_matrix_diagonal {n k : ℕ} (c : PhysicalSpace n)
    (α : MonomialIndex n k) :
    affineCoefficientMap n k c 1 (Pi.single α 1) α = 1 := by
  rw [translation_matrix_entry, ← translatedMonomial_degree MonomialOrder.lex c α]
  exact (translatedMonomial_monic MonomialOrder.lex c α).coeff_degree

/-- Within a degree block, any monomial order refines the triangular form. -/
theorem translation_matrix_monomial_triangular {n k : ℕ} (m : MonomialOrder (Fin n))
    (c : PhysicalSpace n) (α β : MonomialIndex n k)
    (h : m.toSyn (monomialExponent β) < m.toSyn (monomialExponent α)) :
    affineCoefficientMap n k c 1 (Pi.single β 1) α = 0 := by
  rw [translation_matrix_entry]
  apply MonomialOrder.coeff_eq_zero_of_lt (m := m)
  rwa [translatedMonomial_degree]

/-- Translation determinant by degree-block triangularity and unit diagonal. -/
theorem affineCoefficientMap_translation_det_original (n k : ℕ) (c : PhysicalSpace n) :
    LinearMap.det (affineCoefficientMap n k c 1) = 1 := by
  classical
  let M := LinearMap.toMatrix' (affineCoefficientMap n k c 1)
  have hM : M.BlockTriangular (fun α => totalDegree α.val) := by
    intro α β h
    exact translation_matrix_degree_triangular c α β h
  rw [← LinearMap.det_toMatrix']
  change M.det = 1
  rw [hM.det]
  apply Finset.prod_eq_one
  intro r _
  let m : MonomialOrder (Fin n) := MonomialOrder.lex
  letI : LinearOrder {α : MonomialIndex n k // totalDegree α.val = r} :=
    LinearOrder.lift' (fun α => m.toSyn (monomialExponent α.val))
      (m.toSyn.injective.comp ((monomialExponent_injective n k).comp Subtype.val_injective))
  have hb : (M.toSquareBlock (fun α => totalDegree α.val) r).BlockTriangular id := by
    intro α β h
    exact translation_matrix_monomial_triangular m c α.val β.val h
  rw [Matrix.det_of_upperTriangular hb]
  apply Finset.prod_eq_one
  intro α _
  exact translation_matrix_diagonal c α.val

/-- Equal Gram norms give a partial isometry, extended across the kernel.
This avoids dividing by zero singular values. -/
theorem exists_isometry_comp_of_norm_eq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (A C : V →ₗ[ℝ] V) (h : ∀ x, ‖A x‖ = ‖C x‖) :
    ∃ U : V →ₗᵢ[ℝ] V, ∀ x, U (A x) = C x := by
  have hk : LinearMap.ker A ≤ LinearMap.ker C := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    rw [← h x, LinearMap.mem_ker.mp hx, norm_zero]
  let L : LinearMap.range A →ₗ[ℝ] V :=
    ((LinearMap.ker A).liftQ C hk).comp A.quotKerEquivRange.symm.toLinearMap
  have hL (x : V) : L ⟨A x, LinearMap.mem_range_self A x⟩ = C x := by
    simp [L]
  have hn (x : LinearMap.range A) : ‖L x‖ = ‖x‖ := by
    obtain ⟨y, hy⟩ := x.property
    have he : x = ⟨A y, LinearMap.mem_range_self A y⟩ := Subtype.ext hy.symm
    rw [he, hL]
    exact (h y).symm
  let I : LinearMap.range A →ₗᵢ[ℝ] V := { L with norm_map' := hn }
  refine ⟨I.extend, fun x => ?_⟩
  exact (I.extend_apply ⟨A x, LinearMap.mem_range_self A x⟩).trans (hL x)

theorem toEuclideanLin_norm_sq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin B x‖ ^ 2 =
      dotProduct (WithLp.equiv 2 (Fin n → ℝ) x)
        ((B.transpose * B) *ᵥ (WithLp.equiv 2 (Fin n → ℝ) x)) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.piLp_equiv_toEuclideanLin_apply,
    star_trivial]
  conv_rhs => rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Equal right Gram matrices, with no rank or invertibility restriction. -/
theorem sameGram_exists_isometry {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℝ)
    (h : A.transpose * A = C.transpose * C) :
    ∃ U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x, U (Matrix.toEuclideanLin A x) = Matrix.toEuclideanLin C x := by
  apply exists_isometry_comp_of_norm_eq
  intro x
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [toEuclideanLin_norm_sq, toEuclideanLin_norm_sq, h]

/-- Spectral diagonalization of the right Gram matrix gives the right SVD factor,
including zero and repeated singular values. -/
theorem exists_singular_rightGram {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (s : Fin n → ℝ) (V : Matrix (Fin n) (Fin n) ℝ),
      (∀ i, 0 ≤ s i) ∧ V.transpose * V = 1 ∧
      (B * V).transpose * (B * V) = (Matrix.diagonal s).transpose * Matrix.diagonal s := by
  let hG : (B.transpose * B).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self B
  let V : Matrix (Fin n) (Fin n) ℝ := hG.isHermitian.eigenvectorUnitary
  let s : Fin n → ℝ := fun i => Real.sqrt (hG.isHermitian.eigenvalues i)
  refine ⟨s, V, fun i => Real.sqrt_nonneg _, ?_, ?_⟩
  · simpa only [V, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using unitary.coe_star_mul_self hG.isHermitian.eigenvectorUnitary
  · have hg := hG.isHermitian.star_mul_self_mul_eq_diagonal
    change star V * (B.transpose * B) * V = _ at hg
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] at hg
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B.transpose,
      ← Matrix.mul_assoc V.transpose, hg]
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    simpa only [s, pow_two] using (Real.sq_sqrt (hG.eigenvalues_nonneg i)).symm

theorem toEuclideanLin_mul_original {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanLin (A * B) =
      (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  simpa only [Matrix.toEuclideanLin_eq_toLin] using
    Matrix.toLin_mul (PiLp.basisFun 2 ℝ (Fin n)) (PiLp.basisFun 2 ℝ (Fin n))
      (PiLp.basisFun 2 ℝ (Fin n)) A B

/-- Equal right Gram matrices imply an orthogonal left factor, even at deficient rank. -/
theorem sameGram_exists_orthogonal {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℝ)
    (h : A.transpose * A = C.transpose * C) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, U.transpose * U = 1 ∧ C = U * A := by
  obtain ⟨U, hU⟩ := sameGram_exists_isometry A C h
  let e := LinearIsometryEquiv.ofSurjective U
    (LinearMap.surjective_of_injective (f := U.toLinearMap) U.injective)
  refine ⟨isometryMatrix e, isometryMatrix_orthogonal e, ?_⟩
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul_original, toEuclideanLin_isometryMatrix]
  apply LinearMap.ext
  intro x
  exact (hU x).symm

/-- Square real singular-value decomposition, without an invertibility or
simple-spectrum hypothesis. Singular values are nonnegative, with multiplicities. -/
theorem exists_orthogonal_singular_decomposition {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (s : Fin n → ℝ) (U V : Matrix (Fin n) (Fin n) ℝ),
      (∀ i, 0 ≤ s i) ∧ U.transpose * U = 1 ∧ V.transpose * V = 1 ∧
      B = U * Matrix.diagonal s * V.transpose := by
  obtain ⟨s, V, hs, hV, hgram⟩ := exists_singular_rightGram B
  obtain ⟨U, hU, hUV⟩ := sameGram_exists_orthogonal (Matrix.diagonal s) (B * V) hgram.symm
  refine ⟨s, U, V, hs, hU, hV, ?_⟩
  have hVV : V * V.transpose = 1 := Matrix.mul_eq_one_comm.mp hV
  calc
    B = (B * V) * V.transpose := by rw [Matrix.mul_assoc, hVV, Matrix.mul_one]
    _ = U * Matrix.diagonal s * V.transpose := congrArg (fun X => X * V.transpose) hUV

theorem orthogonal_matrix_abs_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose * A = 1) : |A.det| = 1 := by
  have h := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have hs : |A.det| ^ 2 = 1 := by rw [sq_abs, pow_two, h]
  nlinarith [abs_nonneg A.det]

/-- The manuscript's complete centered argument: SVD, orthogonal factors,
homogeneous diagonal blocks, and the hockey-stick identity. -/
theorem affineCoefficientMap_centered_abs_det_original (n k : ℕ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    |LinearMap.det (affineCoefficientMap n k 0 B)| = |B.det| ^ chi n k := by
  cases n with
  | zero => rw [coefficient_det_dim_zero]; simp
  | succ d =>
    obtain ⟨s, U, V, _hs, hU, hV, hB⟩ := exists_orthogonal_singular_decomposition B
    have hVT : V.transpose.transpose * V.transpose = 1 := by
      rw [Matrix.transpose_transpose]
      exact Matrix.mul_eq_one_comm.mp hV
    have hUd := orthogonal_matrix_abs_det U hU
    have hVd := orthogonal_matrix_abs_det V hV
    rw [hB]
    simp only [centeredCoefficientMap_det_mul_original, abs_mul,
      affineCoefficientMap_orthogonal_abs_det_original (d + 1) k U hU,
      affineCoefficientMap_orthogonal_abs_det_original (d + 1) k V.transpose hVT,
      affineCoefficientMap_diagonal_det_original, abs_pow, Matrix.det_mul,
      Matrix.det_transpose, Matrix.det_diagonal, hUd, hVd, one_mul, mul_one]

/-- Full original Lemma 2.1(i), for the unchanged coefficient quotient model. -/
theorem affineCoefficientMap_abs_det_original (n k : ℕ) (c : PhysicalSpace n)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    |LinearMap.det (affineCoefficientMap n k c B)| = |B.det| ^ chi n k := by
  rw [affineCoefficientMap_factor, LinearMap.det_comp,
    affineCoefficientMap_translation_det_original, mul_one]
  exact affineCoefficientMap_centered_abs_det_original n k B

/-- Directly satisfies the existing main-audit contract, without a new premise. -/
theorem affineCharacterStatement_original (n k : ℕ) : AffineCharacterStatement n k :=
  affineCoefficientMap_abs_det_original n k

end PaperI.AllDim.Original
