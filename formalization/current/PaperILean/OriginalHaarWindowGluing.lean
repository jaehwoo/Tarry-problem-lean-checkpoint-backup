import PaperILean.OriginalUpperIntegralBounds

/-! Finite ordered gluing of actual upper-affine increments.
The number of analytic pieces is fixed by the semialgebraic format; the
resulting bound is polynomial for every such fixed number. -/
noncomputable section
namespace PaperI

/-- The actual noncommutative composition includes both translation cross
terms; no commuting-generator or absolute-frame bound is used. -/
theorem originalUpperAffineComp_norm_bound
    (g h : Fin 6 → ℝ) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hg : ‖g‖ ≤ C) (hh : ‖h‖ ≤ R) :
    ‖originalUpperAffineComp g h‖ ≤ C+R+2*C*R := by
  have hgi (i : Fin 6) : |g i| ≤ C := (norm_le_pi_norm g i).trans hg
  have hhi (i : Fin 6) : |h i| ≤ R := (norm_le_pi_norm h i).trans hh
  have hmul (i j : Fin 6) : |g i*h j| ≤ C*R := by
    rw [abs_mul]
    exact mul_le_mul (hgi i) (hhi j) (abs_nonneg _) hC
  have hbase (i : Fin 6) : |g i+h i| ≤ C+R :=
    (abs_add _ _).trans (add_le_add (hgi i) (hhi i))
  have hsum (i j l : Fin 6) : |g i+h i+g j*h l| ≤ C+R+C*R :=
    (abs_add _ _).trans (add_le_add (hbase i) (hmul j l))
  have hsum2 : |g 2+h 2+g 0*h 4+g 1*h 5| ≤ C+R+2*C*R := by
    have h := (abs_add _ _).trans (add_le_add (hsum 2 0 4) (hmul 1 5))
    nlinarith
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · change |g 0+h 0| ≤ _; nlinarith [hbase 0, mul_nonneg hC hR]
  · change |g 1+h 1+g 0*h 3| ≤ _; nlinarith [hsum 1 0 3, mul_nonneg hC hR]
  · exact hsum2
  · change |g 3+h 3| ≤ _; nlinarith [hbase 3, mul_nonneg hC hR]
  · change |g 4+h 4+g 3*h 5| ≤ _; nlinarith [hsum 4 3 5, mul_nonneg hC hR]
  · change |g 5+h 5| ≤ _; nlinarith [hbase 5, mul_nonneg hC hR]

def originalUpperOrderedProduct : List (Fin 6 → ℝ) → (Fin 6 → ℝ)
  | [] => 0
  | g::gs => originalUpperAffineComp g (originalUpperOrderedProduct gs)

/-- The bound retains every finite noncommutative cross term. It is a
polynomial of degree at most the fixed number of pieces. -/
theorem originalUpperOrderedProduct_norm_bound
    (gs : List (Fin 6 → ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hgs : ∀ g ∈ gs, ‖g‖ ≤ R) :
    ‖originalUpperOrderedProduct gs‖+1 ≤ (1+2*R)^gs.length := by
  induction gs with
  | nil => simp [originalUpperOrderedProduct]
  | cons g gs ih =>
    have hg := hgs g (by simp)
    have htail := ih (fun h hh => hgs h (by simp [hh]))
    have hc := originalUpperAffineComp_norm_bound g (originalUpperOrderedProduct gs)
      R ‖originalUpperOrderedProduct gs‖ hR (norm_nonneg _) hg le_rfl
    change ‖originalUpperAffineComp g (originalUpperOrderedProduct gs)‖+1 ≤ _
    calc
      _ ≤ (1+2*R)*(‖originalUpperOrderedProduct gs‖+1) := by nlinarith
      _ ≤ (1+2*R)*(1+2*R)^gs.length :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = (1+2*R)^(g::gs).length := by simp [pow_succ, mul_comm]

/-- The product of successive relative increments telescopes in the stated
order, including arbitrary unbounded absolute starting frames. -/
theorem originalUpperRelativeFrame_comp
    (g h k : Fin 6 → ℝ) :
    originalUpperAffineComp (originalUpperRelativeFrame g h)
      (originalUpperRelativeFrame h k) = originalUpperRelativeFrame g k := by
  ext i
  fin_cases i <;> simp [originalUpperRelativeFrame,originalUpperAffineComp,
    originalUpperAffineInv] <;> ring

/-- A bounded finite chain of actual increments controls the actual relative
endpoint frame, independently of its absolute starting frame. -/
theorem originalUpperRelativeFrame_chain_bound
    (g : ℕ → Fin 6 → ℝ) (n : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hstep : ∀ j<n, ‖originalUpperRelativeFrame (g j) (g (j+1))‖ ≤ R) :
    ‖originalUpperRelativeFrame (g 0) (g n)‖+1 ≤ (1+2*R)^n := by
  induction n with
  | zero => simp [originalUpperRelativeFrame_self]
  | succ n ih =>
    have hp := ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self n)))
    have hs := hstep n (Nat.lt_succ_self n)
    have hc := originalUpperAffineComp_norm_bound
      (originalUpperRelativeFrame (g 0) (g n))
      (originalUpperRelativeFrame (g n) (g (n+1)))
      ‖originalUpperRelativeFrame (g 0) (g n)‖ R (norm_nonneg _) hR le_rfl hs
    rw [originalUpperRelativeFrame_comp] at hc
    calc
      _ ≤ (1+2*R)*(‖originalUpperRelativeFrame (g 0) (g n)‖+1) := by nlinarith
      _ ≤ (1+2*R)*(1+2*R)^n := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (1+2*R)^(n+1) := by rw [pow_succ]; ring

end PaperI
