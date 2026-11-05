import PaperILean.DeterminantRowPerturbation
import PaperILean.MainStatement

/-! I1484[0,122), together with the exact row-perturbation estimate at
I1480[534,674)+I1481-I1483. The tolerance exponent depends only on the
fixed coefficient dimension and the stated row/determinant exponents.
It is chosen before P and all model/actual matrices. All row norms are
Euclidean; arbitrary real source exponents and the empty minor are retained. -/

noncomputable section
namespace PaperI.SamplingDeterminantStability

/-- The explicit exponent for any minor of size at most N. -/
noncomputable def toleranceExponent (N : ℕ) (Cm Cb : ℝ) : ℝ :=
  (N : ℝ) + (N : ℝ) * (max Cm 0 + 1) + max Cb 0 + 1

/-- The source exponent, fixed by degree and source quantitative bounds. -/
noncomputable def samplingToleranceExponent (k : ℕ) (Cm Cb : ℝ) : ℝ :=
  toleranceExponent (dimension k) Cm Cb

theorem toleranceExponent_nonneg (N : ℕ) (Cm Cb : ℝ) :
    0 ≤ toleranceExponent N Cm Cb := by
  unfold toleranceExponent
  positivity

/-- The prescribed tolerance is positive and at most one. -/
theorem tolerance_pos_le_one (N : ℕ) (Cm Cb P : ℝ) (hP : 2 ≤ P) :
    0 < P ^ (-toleranceExponent N Cm Cb) ∧
      P ^ (-toleranceExponent N Cm Cb) ≤ 1 := by
  have hpos : 0 < P := by linarith
  refine ⟨Real.rpow_pos_of_pos hpos _, ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
    (neg_nonpos.mpr (toleranceExponent_nonneg N Cm Cb))

/-- Uniform power arithmetic for the literal determinant error, with the
minor size bounded before any matrix is supplied. -/
theorem tolerance_error_bound (N n : ℕ) (hn : n ≤ N)
    (P Cm Cb M : ℝ) (hP : 2 ≤ P) (hM : 0 ≤ M) (hwindow : M ≤ P ^ Cm) :
    (n : ℝ) * P ^ (-toleranceExponent N Cm Cb) * (M + 1) ^ (n - 1) ≤
      P ^ (-Cb) / 2 := by
  have hpos : 0 < P := by linarith
  have hone : 1 ≤ P := by linarith
  have hα : 0 ≤ max Cm 0 := le_max_right _ _
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hNtwo : (N : ℝ) ≤ (2 : ℝ) ^ N := by
    have hs : N < 2 ^ N := Nat.lt_two_pow_self
    exact_mod_cast hs.le
  have hnP : (n : ℝ) ≤ P ^ (N : ℝ) := by
    rw [Real.rpow_natCast]
    exact hnN.trans (hNtwo.trans (pow_le_pow_left₀ (by norm_num) hP N))
  have hMα : M ≤ P ^ (max Cm 0) := hwindow.trans
    (Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _))
  have hunit : 1 ≤ P ^ (max Cm 0) := Real.one_le_rpow hone hα
  have hMone : M + 1 ≤ P ^ (max Cm 0 + 1) := by
    calc
      _ ≤ 2 * P ^ (max Cm 0) := by linarith
      _ ≤ P * P ^ (max Cm 0) :=
        mul_le_mul_of_nonneg_right hP (Real.rpow_nonneg hpos.le _)
      _ = P ^ (max Cm 0 + 1) := by rw [Real.rpow_add hpos, Real.rpow_one]; ring
  have hbase : 1 ≤ P ^ (max Cm 0 + 1) := Real.one_le_rpow hone (by positivity)
  have hpow : (M + 1) ^ (n - 1) ≤ P ^ ((N : ℝ) * (max Cm 0 + 1)) := by
    calc
      _ ≤ (P ^ (max Cm 0 + 1)) ^ (n - 1) :=
        pow_le_pow_left₀ (by linarith) hMone _
      _ ≤ (P ^ (max Cm 0 + 1)) ^ N :=
        pow_le_pow_right₀ hbase ((Nat.sub_le n 1).trans hn)
      _ = P ^ ((N : ℝ) * (max Cm 0 + 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
        congr 1
        ring
  have hε : 0 ≤ P ^ (-toleranceExponent N Cm Cb) := Real.rpow_nonneg hpos.le _
  calc
    _ ≤ P ^ (N : ℝ) * P ^ (-toleranceExponent N Cm Cb) *
        P ^ ((N : ℝ) * (max Cm 0 + 1)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hnP hε) hpow
        (pow_nonneg (by linarith) _) (mul_nonneg (Real.rpow_nonneg hpos.le _) hε)
    _ = P ^ (-max Cb 0 - 1) := by
      rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]
      congr 1
      unfold toleranceExponent
      ring
    _ = P ^ (-max Cb 0) / P := by rw [Real.rpow_sub hpos, Real.rpow_one]
    _ ≤ P ^ (-Cb) / P := by
      apply div_le_div_of_nonneg_right _ hpos.le
      exact Real.rpow_le_rpow_of_exponent_le hone (neg_le_neg (le_max_left _ _))
    _ ≤ P ^ (-Cb) / 2 :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hpos.le _) (by norm_num) hP

/-- The nonnegative-window form used for a nonempty minor. The public stage
below derives nonnegativity from an actual row and handles the empty case. -/
theorem sampling_determinant_stability_stage_of_nonneg (k : ℕ) (_hk : 2 ≤ k) (Cm Cb : ℝ)
    (P M b : ℝ) (n : ℕ) (B A : Matrix (Fin n) (Fin n) ℝ)
    (hn : n ≤ dimension k) (hP : 2 ≤ P) (hM : 0 ≤ M) (hwindow : M ≤ P ^ Cm)
    (hb : P ^ (-Cb) ≤ b) (hdet : b ≤ |B.det|)
    (hrows : ∀ i, coordinateL2Norm (B i) ≤ M)
    (herror : ∀ i, coordinateL2Norm (A i - B i) ≤
      P ^ (-samplingToleranceExponent k Cm Cb)) :
    |B.det| / 2 ≤ |A.det| ∧ b / 2 ≤ |A.det| ∧ A.det ≠ 0 := by
  have hε := tolerance_pos_le_one (dimension k) Cm Cb P hP
  have herr := DeterminantRowPerturbation.determinant_row_perturbation n B A M
    (P ^ (-samplingToleranceExponent k Cm Cb)) hε.2 hrows herror
  have hscalar := tolerance_error_bound (dimension k) n hn P Cm Cb M hP hM hwindow
  change (n : ℝ) * P ^ (-samplingToleranceExponent k Cm Cb) * (M + 1) ^ (n - 1) ≤
    P ^ (-Cb) / 2 at hscalar
  have herrhalf : |A.det - B.det| ≤ b / 2 :=
    (herr.trans hscalar).trans (div_le_div_of_nonneg_right hb (by norm_num))
  have hreverse : |B.det| - |A.det| ≤ |A.det - B.det| := by
    simpa only [abs_sub_comm] using abs_sub_abs_le_abs_sub B.det A.det
  have hkeep : |B.det| / 2 ≤ |A.det| := by linarith
  have hkeepb : b / 2 ≤ |A.det| := by linarith
  have hpos : 0 < P := by linarith
  have hbpos : 0 < b := (Real.rpow_pos_of_pos hpos (-Cb)).trans_le hb
  exact ⟨hkeep, hkeepb, abs_pos.mp (by linarith)⟩

/-- Complete source determinant-stability stage. The tolerance is fixed
before P, the minor size and both matrices. No determinant lower bound for
the actual matrix is assumed. An empty minor retains arbitrary M, since
its row bounds are vacuous and both determinants equal one. -/
theorem sampling_determinant_stability_stage (k : ℕ) (hk : 2 ≤ k) (Cm Cb : ℝ)
    (P M b : ℝ) (n : ℕ) (B A : Matrix (Fin n) (Fin n) ℝ)
    (hn : n ≤ dimension k) (hP : 2 ≤ P) (hwindow : M ≤ P ^ Cm)
    (hb : P ^ (-Cb) ≤ b) (hdet : b ≤ |B.det|)
    (hrows : ∀ i, coordinateL2Norm (B i) ≤ M)
    (herror : ∀ i, coordinateL2Norm (A i - B i) ≤
      P ^ (-samplingToleranceExponent k Cm Cb)) :
    |B.det| / 2 ≤ |A.det| ∧ b / 2 ≤ |A.det| ∧ A.det ≠ 0 := by
  cases n with
  | zero =>
      have hb1 : b ≤ 1 := by simpa using hdet
      have hhalf : b / 2 ≤ 1 := by linarith
      simpa using (show (1 : ℝ) / 2 ≤ 1 ∧ b / 2 ≤ 1 ∧ (1 : ℝ) ≠ 0 from
        ⟨by norm_num, hhalf, by norm_num⟩)
  | succ n =>
      have hM : 0 ≤ M := (coordinateL2Norm_nonneg (B 0)).trans (hrows 0)
      exact sampling_determinant_stability_stage_of_nonneg k hk Cm Cb P M b
        (n + 1) B A hn hP hM hwindow hb hdet hrows herror

end PaperI.SamplingDeterminantStability
