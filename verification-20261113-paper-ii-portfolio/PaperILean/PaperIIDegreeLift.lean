import PaperILean.AllDimAffinePullback
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Paper II, II1567–II1576. The rows of the two chosen sampling minors
are retained in old-before-new order, and the top-degree block uses the
linear parts of the same sample states. -/

open scoped BigOperators Classical

noncomputable section

namespace PaperII.DegreeLift

open MvPolynomial
open PaperI.AllDim

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℝ

private theorem degree_pow_of_linear_bound {n : ℕ} {p : Poly n}
    (hp : p.totalDegree ≤ 1) (r : ℕ) : (p ^ r).totalDegree ≤ r :=
  (totalDegree_pow p r).trans (by simpa using Nat.mul_le_mul_left r hp)

private theorem degree_pow_sub_of_constant_difference {n : ℕ} (p q : Poly n)
    (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1)
    (hc : (p - q).totalDegree = 0) (r : ℕ) :
    (p ^ (r + 1) - q ^ (r + 1)).totalDegree < r + 1 := by
  induction r with
  | zero => simp [hc]
  | succ r ih =>
      have hsplit : p ^ (r + 1 + 1) - q ^ (r + 1 + 1) =
          (p ^ (r + 1) - q ^ (r + 1)) * p + q ^ (r + 1) * (p - q) := by
        rw [pow_succ p, pow_succ q]
        ring
      rw [show r.succ + 1 = r + 1 + 1 by rfl, hsplit]
      apply (totalDegree_add _ _).trans_lt
      apply max_lt
      · exact (totalDegree_mul _ _).trans_lt (by omega)
      · have hqpow := degree_pow_of_linear_bound hq (r + 1)
        exact (totalDegree_mul _ _).trans_lt (by omega)

private theorem degree_prod_of_linear_bounds {n : ℕ} {ι : Type*}
    (s : Finset ι) (p : ι → Poly n) (e : ι → ℕ)
    (hp : ∀ i, (p i).totalDegree ≤ 1) :
    (∏ i ∈ s, p i ^ e i).totalDegree ≤ ∑ i ∈ s, e i :=
  (totalDegree_finset_prod s _).trans
    (Finset.sum_le_sum fun i _ => degree_pow_of_linear_bound (hp i) (e i))

private theorem degree_prod_sub_of_constant_differences {n : ℕ} {ι : Type*}
    (s : Finset ι) (p q : ι → Poly n) (e : ι → ℕ)
    (hp : ∀ i, (p i).totalDegree ≤ 1) (hq : ∀ i, (q i).totalDegree ≤ 1)
    (hc : ∀ i, (p i - q i).totalDegree = 0)
    (hs : 0 < ∑ i ∈ s, e i) :
    ((∏ i ∈ s, p i ^ e i) - ∏ i ∈ s, q i ^ e i).totalDegree < ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a t hat ih =>
      rw [Finset.sum_insert hat] at hs ⊢
      rw [Finset.prod_insert hat, Finset.prod_insert hat]
      by_cases ha : e a = 0
      · simp only [ha, pow_zero, one_mul, zero_add] at hs ⊢
        exact ih hs
      · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero ha
        have hd := degree_pow_sub_of_constant_difference (p a) (q a) (hp a) (hq a) (hc a) r
        rw [← Nat.succ_eq_add_one, ← hr] at hd
        let P := ∏ i ∈ t, p i ^ e i
        let Q := ∏ i ∈ t, q i ^ e i
        change (p a ^ e a * P - q a ^ e a * Q).totalDegree < e a + ∑ i ∈ t, e i
        have hsplit : p a ^ e a * P - q a ^ e a * Q =
            (p a ^ e a - q a ^ e a) * P + q a ^ e a * (P - Q) := by ring
        rw [hsplit]
        apply (totalDegree_add _ _).trans_lt
        apply max_lt
        · have hP := degree_prod_of_linear_bounds t p e hp
          exact (totalDegree_mul _ _).trans_lt (by change P.totalDegree ≤ _ at hP; omega)
        · by_cases ht : (∑ i ∈ t, e i) = 0
          · have he : ∀ i ∈ t, e i = 0 := by
              intro i hi
              have hle : e i ≤ ∑ j ∈ t, e j :=
                Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
              omega
            have hP : P = 1 := Finset.prod_eq_one fun i hi => by rw [he i hi, pow_zero]
            have hQ : Q = 1 := Finset.prod_eq_one fun i hi => by rw [he i hi, pow_zero]
            rw [hP, hQ, sub_self, mul_zero, totalDegree_zero, ht]
            omega
          · have hdiff : (P - Q).totalDegree < ∑ i ∈ t, e i := ih (Nat.pos_of_ne_zero ht)
            have hqpow := degree_pow_of_linear_bound (hq a) (e a)
            exact (totalDegree_mul _ _).trans_lt (by omega)

/-- A leading monomial coefficient of an actual affine pullback equals that
of its centered linear pullback. No nonzero determinant hypothesis is used. -/
theorem affine_leading_monomial_coeff {n : ℕ} (c : PhysicalSpace n)
    (B : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n →₀ ℕ) (ha : 0 < a.degree)
    (hab : a.degree = b.degree) :
    coeff b (affinePolynomialMap c B (monomial a (1 : ℝ))) =
      coeff b (affinePolynomialMap 0 B (monomial a (1 : ℝ))) := by
  classical
  have hsum (d : Fin n →₀ ℕ) : d.degree = ∑ i, d i :=
    Finsupp.sum_fintype d (fun _ e => e) (fun _ => rfl)
  have hpos : 0 < ∑ i, a i := hsum a ▸ ha
  have hdiff i :
      (affineCoordinate c B i - affineCoordinate 0 B i).totalDegree = 0 := by
    have heq : affineCoordinate c B i - affineCoordinate 0 B i = C (c i) := by
      simp [affineCoordinate]
    rw [heq, totalDegree_C]
  have hlt := degree_prod_sub_of_constant_differences Finset.univ
    (affineCoordinate c B) (affineCoordinate 0 B) a
    (affineCoordinate_degree c B) (affineCoordinate_degree 0 B) hdiff hpos
  rw [← hsum a, hab] at hlt
  have hz := coeff_eq_zero_of_totalDegree_lt (d := b) hlt
  rw [coeff_sub] at hz
  simpa [affinePolynomialMap, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    using sub_eq_zero.mp hz

/-- The new columns and output rows use all homogeneous monomials of degree
`k+1`. The old columns use the manuscript's nonconstant coefficient basis. -/
def TopIndex (n k : ℕ) := {a : MonomialIndex n (k + 1) // totalDegree a.val = k + 1}

instance (n k : ℕ) : Fintype (TopIndex n k) := by
  classical
  unfold TopIndex
  infer_instance

/-- The old positive-degree monomials embed into the larger quotient. -/
def oldColumn {n k : ℕ} (a : MonomialIndex n k) : MonomialIndex n (k + 1) :=
  ⟨fun i => (a.val i).castLE (Nat.le_succ (k + 1)),
    ⟨a.property.1, a.property.2.trans (Nat.le_succ k)⟩⟩

@[simp] theorem exponent_oldColumn {n k : ℕ} (a : MonomialIndex n k) :
    monomialExponent (oldColumn a) = monomialExponent a := by
  ext i
  rfl

private theorem degree_monomialExponent {n k : ℕ} (a : MonomialIndex n k) :
    (monomialExponent a).degree = totalDegree a.val :=
  sum_monomialExponent a

/-- Concatenating the two column lists gives exactly the complete
positive-degree basis at the larger degree. -/
def combinedColumns (n k : ℕ) :
    MonomialIndex n k ⊕ TopIndex n k ≃ MonomialIndex n (k + 1) where
  toFun := Sum.elim oldColumn Subtype.val
  invFun a := if ha : totalDegree a.val ≤ k then
    Sum.inl ⟨fun i => ⟨(a.val i).val, Nat.lt_succ_of_le
      ((exponent_le_sum (monomialExponent a) i).trans
        ((sum_monomialExponent a).trans_le ha))⟩,
      ⟨a.property.1, ha⟩⟩
    else Sum.inr ⟨a, le_antisymm a.property.2 (by omega)⟩
  left_inv a := by
    rcases a with a | a
    · change (if h : totalDegree (oldColumn a).val ≤ k then _ else _) = _
      have ha : totalDegree (oldColumn a).val ≤ k := a.property.2
      simp only [Sum.elim_inl, dif_pos ha]
      rfl
    · change (if h : totalDegree a.val.val ≤ k then _ else _) = _
      have ha : ¬ totalDegree a.val.val ≤ k := by rw [a.property]; omega
      simp only [Sum.elim_inr, dif_neg ha]
      rfl
  right_inv a := by
    dsimp only
    split
    · apply Subtype.ext
      funext i
      exact Fin.ext rfl
    · rfl

/-- A sampled row is the indicated actual coefficient after the affine
substitution at its fixed sample state. As every retained output exponent
has positive degree, removing the constant coefficient has no effect. -/
def sampleEntry {n : ℕ} (c : PhysicalSpace n) (B : Matrix (Fin n) (Fin n) ℝ)
    (row col : Fin n →₀ ℕ) : ℝ :=
  coeff row (affinePolynomialMap c B (monomial col 1))

private theorem exponent_injective {n k : ℕ} :
    Function.Injective (@monomialExponent n k) :=
  fun _ _ h => (monomialIndexEquiv n k).injective (Subtype.ext h)

private theorem coeff_coefficientPolynomial {n k : ℕ} (F : CoefficientSpace n k)
    (a : MonomialIndex n k) : coeff (monomialExponent a) (coefficientPolynomial F) = F a := by
  rw [coefficientPolynomial_eq_sum, coeff_sum]
  simp [coeff_monomial, exponent_injective.eq_iff]

/-- A matrix entry uses the actual nonconstant coefficient of a pulled-back
basis monomial in the existing coefficient quotient. -/
theorem sampleEntry_eq_affineCoefficientMap {n k : ℕ} (c : PhysicalSpace n)
    (B : Matrix (Fin n) (Fin n) ℝ) (row col : MonomialIndex n k) :
    sampleEntry c B (monomialExponent row) (monomialExponent col) =
      affineCoefficientMap n k c B (Pi.single col (1 : ℝ)) row := by
  have hpoly : coefficientPolynomial (Pi.single col (1 : ℝ)) =
      monomial (monomialExponent col) 1 := by
    rw [coefficientPolynomial_eq_sum, Finset.sum_eq_single col]
    · simp
    · intro a _ ha
      simp [Pi.single_eq_of_ne ha]
    · simp
  have hne : monomialExponent row ≠ 0 := by
    intro hzero
    have hpos := row.property.1
    rw [← degree_monomialExponent, hzero, Finsupp.degree_zero] at hpos
    exact (by omega)
  rw [← coeff_coefficientPolynomial (affineCoefficientMap n k c B (Pi.single col 1)) row,
    polynomial_affineCoefficientMap, hpoly, coeff_sub]
  simp [sampleEntry, coeff_C, hne, Ne.symm hne]

/-- The selected rows of the degree-at-most-`k` coefficient minor. -/
def lowerMinor {n k : ℕ} {ι : Type*} (c : ι → PhysicalSpace n)
    (B : ι → Matrix (Fin n) (Fin n) ℝ)
    (rows : MonomialIndex n k ↪ ι × MonomialIndex n k) :
    Matrix (MonomialIndex n k) (MonomialIndex n k) ℝ :=
  fun i j => sampleEntry (c (rows i).1) (B (rows i).1)
    (monomialExponent (rows i).2) (monomialExponent j)

/-- The chosen top-degree rows at the linear parts of the same states. -/
def homogeneousMinor {n k : ℕ} {ι : Type*} (B : ι → Matrix (Fin n) (Fin n) ℝ)
    (rows : TopIndex n k ↪ ι × TopIndex n k) :
    Matrix (TopIndex n k) (TopIndex n k) ℝ :=
  fun i j => sampleEntry 0 (B (rows i).1)
    (monomialExponent (rows i).2.val) (monomialExponent j.val)

/-- The two selected lists inject into the actual rows at the larger
degree. The old and new lists cannot share a row because their degrees differ. -/
def combinedRows {n k : ℕ} {ι : Type*}
    (lowerRows : MonomialIndex n k ↪ ι × MonomialIndex n k)
    (topRows : TopIndex n k ↪ ι × TopIndex n k) :
    (MonomialIndex n k ⊕ TopIndex n k) ↪ ι × MonomialIndex n (k + 1) where
  toFun := Sum.elim
    (fun x => ((lowerRows x).1, oldColumn (lowerRows x).2))
    (fun x => ((topRows x).1, (topRows x).2.val))
  inj' := by
    intro i j hij
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            apply congrArg Sum.inl
            apply lowerRows.injective
            have hsample : (lowerRows i).1 = (lowerRows j).1 :=
              congrArg (Prod.fst : ι × MonomialIndex n (k + 1) → ι) hij
            have hcol : combinedColumns n k (.inl (lowerRows i).2) =
                combinedColumns n k (.inl (lowerRows j).2) := congrArg Prod.snd hij
            exact Prod.ext hsample (Sum.inl.inj ((combinedColumns n k).injective hcol))
        | inr j =>
            have hcol : combinedColumns n k (.inl (lowerRows i).2) =
                combinedColumns n k (.inr (topRows j).2) := congrArg Prod.snd hij
            cases (combinedColumns n k).injective hcol
    | inr i =>
        cases j with
        | inl j =>
            have hcol : combinedColumns n k (.inr (topRows i).2) =
                combinedColumns n k (.inl (lowerRows j).2) := congrArg Prod.snd hij
            cases (combinedColumns n k).injective hcol
        | inr j =>
            apply congrArg Sum.inr
            apply topRows.injective
            have hsample : (topRows i).1 = (topRows j).1 :=
              congrArg (Prod.fst : ι × MonomialIndex n (k + 1) → ι) hij
            have hcol : (topRows i).2.val = (topRows j).2.val := congrArg Prod.snd hij
            exact Prod.ext hsample (Subtype.ext hcol)

/-- Both row lists, using the original affine samples and the complete
column basis in old-before-new order. -/
def combinedMinor {n k : ℕ} {ι : Type*} (c : ι → PhysicalSpace n)
    (B : ι → Matrix (Fin n) (Fin n) ℝ)
    (lowerRows : MonomialIndex n k ↪ ι × MonomialIndex n k)
    (topRows : TopIndex n k ↪ ι × TopIndex n k) :
    Matrix (MonomialIndex n k ⊕ TopIndex n k) (MonomialIndex n k ⊕ TopIndex n k) ℝ :=
  fun i j =>
    let row := combinedRows lowerRows topRows i
    sampleEntry (c row.1) (B row.1) (monomialExponent row.2)
      (monomialExponent (combinedColumns n k j))

/-- The actual combined sampling matrix has the exact block form in II1573.
Translations can occur in the upper-right block, which is unrestricted. -/
theorem combinedMinor_eq_blocks {n k : ℕ} {ι : Type*} (c : ι → PhysicalSpace n)
    (B : ι → Matrix (Fin n) (Fin n) ℝ)
    (lowerRows : MonomialIndex n k ↪ ι × MonomialIndex n k)
    (topRows : TopIndex n k ↪ ι × TopIndex n k) :
    ∃ upper : Matrix (MonomialIndex n k) (TopIndex n k) ℝ,
      combinedMinor c B lowerRows topRows =
        Matrix.fromBlocks (lowerMinor c B lowerRows) upper 0 (homogeneousMinor B topRows) := by
  classical
  refine ⟨fun i j => combinedMinor c B lowerRows topRows (.inl i) (.inr j), ?_⟩
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => simp [combinedMinor, combinedRows, lowerMinor, combinedColumns]
      | inr j => rfl
  | inr i =>
      cases j with
      | inl j =>
          rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
          change sampleEntry (c (topRows i).1) (B (topRows i).1)
            (monomialExponent (topRows i).2.val) (monomialExponent (oldColumn j)) = 0
          rw [exponent_oldColumn]
          apply coeff_eq_zero_of_totalDegree_lt
          refine (affinePolynomialMap_degree _ _ _).trans_lt ?_
          refine (totalDegree_monomial_le _ _).trans_lt ?_
          change (monomialExponent j).degree < (monomialExponent (topRows i).2.val).degree
          rw [degree_monomialExponent, degree_monomialExponent, (topRows i).2.property]
          exact Nat.lt_succ_of_le j.property.2
      | inr j =>
          rw [Matrix.fromBlocks_apply₂₂]
          apply affine_leading_monomial_coeff
          · change 0 < (monomialExponent j.val).degree
            rw [degree_monomialExponent, j.property]
            exact Nat.zero_lt_succ k
          · change (monomialExponent j.val).degree = (monomialExponent (topRows i).2.val).degree
            rw [degree_monomialExponent, degree_monomialExponent, j.property,
              (topRows i).2.property]

/-- Paper II II1567–II1569, with no additional theorem inputs. A parameter
`k` denotes the old degree, so the source's degree `k` is `k+1` here.
The old degree-zero coefficient space is allowed and has no columns. -/
theorem block_triangular_degree_lift {n k : ℕ} {ι : Type*}
    (c : ι → PhysicalSpace n) (B : ι → Matrix (Fin n) (Fin n) ℝ)
    (lowerRows : MonomialIndex n k ↪ ι × MonomialIndex n k)
    (topRows : TopIndex n k ↪ ι × TopIndex n k) :
    (combinedMinor c B lowerRows topRows).det =
      (lowerMinor c B lowerRows).det * (homogeneousMinor B topRows).det := by
  obtain ⟨upper, hblocks⟩ := combinedMinor_eq_blocks c B lowerRows topRows
  rw [hblocks, Matrix.det_fromBlocks_zero₂₁]

end PaperII.DegreeLift
