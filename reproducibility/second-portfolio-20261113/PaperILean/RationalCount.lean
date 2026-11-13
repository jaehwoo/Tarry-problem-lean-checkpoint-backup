import PaperILean.RationalCountDifferential

/-! S515 (from "For a fixed y")--S517: exact clearing of rational fibers and
the original nonsingular polynomial zero-count application. The only cited
input is the standard polynomial-only nonsingular Bezout theorem. -/
noncomputable section
open scoped BigOperators
namespace PaperI.RationalCount

/-- The polynomial Jacobian in the cited source uses the transposed
index convention. Its determinant and nonsingularity condition agree. -/
theorem polynomialJacobian_transpose_det {k : ℕ}
    (G : Fin k → MvPolynomial (Fin k) ℝ) (x : Fin k → ℝ) :
    (polynomialJacobian G x).transpose.det = (polynomialJacobian G x).det :=
  Matrix.det_transpose _

theorem cleared_zero_iff_fiber {k : ℕ}
    (P Q : Fin k → MvPolynomial (Fin k) ℝ) (x y : Fin k → ℝ)
    (hden : ∀ i, MvPolynomial.eval x (Q i) ≠ 0) :
    (∀ i, MvPolynomial.eval x (cleared P Q y i) = 0) ↔ rationalMap P Q x = y := by
  constructor
  · intro hzero
    funext i
    change MvPolynomial.eval x (P i) / MvPolynomial.eval x (Q i) = y i
    apply (div_eq_iff (hden i)).mpr
    apply sub_eq_zero.mp
    simpa only [cleared,map_sub,map_mul,MvPolynomial.eval_C] using hzero i
  · exact cleared_eval_zero P Q x y hden

/-- Real positive-degree instance of classical nonsingular Bezout. Sources:
Yomdin--Comte, LNM 1834, Proposition 4.6, p.49; Bafna--Sudan--Velusamy--Xiang,
arXiv:2102.00602v1, Definition 1.1 and Corollary 1.3. This is a named external
input, not a global axiom or an inhabitant. Its statement mentions only global
polynomial systems, never a rational map, domain, fiber or manuscript claim. -/
structure PublishedNonsingularBezout : Prop where
  bounded_roots : ∀ (k D : ℕ), 0 < k → 0 < D →
    ∀ G : Fin k → MvPolynomial (Fin k) ℝ,
      (∀ i, (G i).totalDegree ≤ D) →
      ∃ s : Finset (Fin k → ℝ),
        (∀ x, x ∈ s ↔ (∀ i, MvPolynomial.eval x (G i) = 0) ∧
          (polynomialJacobian G x).det ≠ 0) ∧ s.card ≤ D ^ k

theorem cleared_totalDegree {k D : ℕ}
    (P Q : Fin k → MvPolynomial (Fin k) ℝ) (y : Fin k → ℝ)
    (hP : ∀ i, (P i).totalDegree ≤ D) (hQ : ∀ i, (Q i).totalDegree ≤ D)
    (i : Fin k) : (cleared P Q y i).totalDegree ≤ D := by
  unfold cleared
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le (hP i)
  have hmul : (MvPolynomial.C (y i) * Q i).totalDegree ≤ (Q i).totalDegree := by
    simpa only [MvPolynomial.smul_eq_C_mul] using
      (MvPolynomial.totalDegree_smul_le (y i) (Q i))
  exact hmul.trans (hQ i)

theorem polynomialJacobian_zero_of_degree_zero {k : ℕ}
    (G : Fin k → MvPolynomial (Fin k) ℝ)
    (hG : ∀ i, (G i).totalDegree ≤ 0) (x : Fin k → ℝ) :
    polynomialJacobian G x = 0 := by
  ext i j
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (hG i))
  change MvPolynomial.eval x (MvPolynomial.pderiv j (G i)) = 0
  rw [hc,MvPolynomial.pderiv_C,map_zero]

theorem polynomialJacobian_det_zero_of_degree_zero {k : ℕ} (hk : 0 < k)
    (G : Fin k → MvPolynomial (Fin k) ℝ)
    (hG : ∀ i, (G i).totalDegree ≤ 0) (x : Fin k → ℝ) :
    (polynomialJacobian G x).det = 0 := by
  rw [polynomialJacobian_zero_of_degree_zero G hG x]
  exact Matrix.det_zero ⟨⟨0,hk⟩⟩

def nonsingularFiber {k : ℕ} (U : Set (Fin k → ℝ))
    (P Q : Fin k → MvPolynomial (Fin k) ℝ) (y : Fin k → ℝ) : Set (Fin k → ℝ) :=
  {x | x ∈ U ∧ rationalMap P Q x = y ∧ (rationalJacobian P Q x).det ≠ 0}

/-- Complete S515--S517 regular-fiber count, including degree zero. The open
domain is retained from the source. No finite-zero-set hypothesis is assumed. -/
theorem rational_nonsingular_fiber_count
    (cited : PublishedNonsingularBezout) {k D : ℕ} (hk : 0 < k)
    (U : Set (Fin k → ℝ)) (_hU : IsOpen U)
    (P Q : Fin k → MvPolynomial (Fin k) ℝ) (y : Fin k → ℝ)
    (hP : ∀ i, (P i).totalDegree ≤ D) (hQ : ∀ i, (Q i).totalDegree ≤ D)
    (hden : ∀ x ∈ U, ∀ i, MvPolynomial.eval x (Q i) ≠ 0) :
    ∃ s : Finset (Fin k → ℝ),
      (∀ x, x ∈ s ↔ x ∈ nonsingularFiber U P Q y) ∧ s.card ≤ D ^ k := by
  classical
  by_cases hD : D = 0
  · subst D
    refine ⟨∅,?_,by simp [hk.ne']⟩
    intro x
    simp only [Finset.not_mem_empty, false_iff]
    intro hx
    have hnon := cleared_jacobian_det_ne_zero P Q x y (hden x hx.1) hx.2.1 hx.2.2
    have hzero := polynomialJacobian_det_zero_of_degree_zero hk (cleared P Q y)
      (cleared_totalDegree P Q y hP hQ) x
    exact hnon hzero
  · obtain ⟨s,hs,hcard⟩ := cited.bounded_roots k D hk (Nat.pos_of_ne_zero hD)
      (cleared P Q y) (cleared_totalDegree P Q y hP hQ)
    refine ⟨s.filter (fun x => x ∈ nonsingularFiber U P Q y),?_,?_⟩
    · intro x
      simp only [Finset.mem_filter]
      constructor
      · exact And.right
      · intro hx
        refine ⟨(hs x).mpr ⟨?_,?_⟩,hx⟩
        · exact cleared_eval_zero P Q x y (hden x hx.1) hx.2.1
        · exact cleared_jacobian_det_ne_zero P Q x y (hden x hx.1) hx.2.1 hx.2.2
    · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard

/-- Apply the completed stage to any fixed k-coordinate projection of an
n-component rational map. No degree growth comes from selecting coordinates. -/
theorem rational_projected_nonsingular_fiber_count
    (cited : PublishedNonsingularBezout) {k n D : ℕ} (hk : 0 < k) (_hkn : k ≤ n)
    (U : Set (Fin k → ℝ)) (hU : IsOpen U)
    (P Q : Fin n → MvPolynomial (Fin k) ℝ) (ρ : Fin k → Fin n) (y : Fin k → ℝ)
    (hP : ∀ i, (P i).totalDegree ≤ D) (hQ : ∀ i, (Q i).totalDegree ≤ D)
    (hden : ∀ x ∈ U, ∀ i, MvPolynomial.eval x (Q i) ≠ 0) :
    ∃ s : Finset (Fin k → ℝ),
      (∀ x, x ∈ s ↔ x ∈ nonsingularFiber U (P ∘ ρ) (Q ∘ ρ) y) ∧
      s.card ≤ D ^ k := by
  exact rational_nonsingular_fiber_count cited hk U hU (P ∘ ρ) (Q ∘ ρ) y
    (fun i => hP (ρ i)) (fun i => hQ (ρ i)) (fun x hx i => hden x hx (ρ i))

end PaperI.RationalCount
