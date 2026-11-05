import PaperILean.OriginalDGaugeWidths
import PaperILean.OriginalUpperNormalization

/-! I1560[75,277)+I1560[347,675): the actual residual coefficients in
the parabolic and cubic local dilations. The source raw suprema are
retained before maxima with one. No model-covering assertion is made. -/

noncomputable section
namespace PaperI.DComparisonCoefficients
open OriginalDGauge OriginalDGaugeWidths OriginalUpperNormalization
open AffineNormalizationMatrices

def mixedRate (g v : ℝ → Fin 6 → ℝ) (t : ℝ) : ℝ :=
  originalAffineBodyCoordinates (g t) (v t) 2 -
    originalAffineBodyCoordinates (g t) (v t) 1 *
      originalAffineBodyCoordinates (g t) (v t) 4

/-- Actual body coefficients, extracted from the genuine path derivative. -/
def pathBody (q : ℝ → Fin 6 → ℝ) (s : ℝ) : Fin 6 → ℝ :=
  originalAffineBodyCoordinates (q s) (deriv q s)

def parabolicPath (g : ℝ → Fin 6 → ℝ) (beta eta : ℝ → ℝ)
    (t0 H theta w : ℝ) : ℝ → Fin 6 → ℝ :=
  normalizedUpperPath (gaugedPath g beta eta) t0 (theta*H)
    (theta*H) (theta^2*H*w) (theta*w)

def cubicPath (g : ℝ → Fin 6 → ℝ) (beta eta : ℝ → ℝ)
    (t0 H theta u w : ℝ) : ℝ → Fin 6 → ℝ :=
  normalizedUpperPath (gaugedPath g beta eta) t0 (theta*H)
    (theta^3*H*u*w) (theta^2*H*w) (theta*w)

private theorem normalized_gauge_body
    (g v : ℝ → Fin 6 → ℝ) (beta eta dbeta deta : ℝ → ℝ)
    (t0 h sx sy sz s : ℝ) (hsx : sx ≠ 0) (hsy : sy ≠ 0) (hsz : sz ≠ 0)
    (hg : HasDerivAt g (v (t0+h*s)) (t0+h*s))
    (hb : HasDerivAt beta (dbeta (t0+h*s)) (t0+h*s))
    (he : HasDerivAt eta (deta (t0+h*s)) (t0+h*s))
    (hbeta : beta (t0+h*s) = originalAffineBodyCoordinates (g (t0+h*s)) (v (t0+h*s)) 1)
    (heta : eta (t0+h*s) = originalAffineBodyCoordinates (g (t0+h*s)) (v (t0+h*s)) 4)
    (hD : originalAffineBodyCoordinates (g (t0+h*s)) (v (t0+h*s)) 3 = 1) :
    pathBody (normalizedUpperPath (gaugedPath g beta eta) t0 h sx sy sz) s =
      normalizedBodyRates h sx sy sz
        (gaugeBodyRates (originalAffineBodyCoordinates (g (t0+h*s)) (v (t0+h*s)))
          (dbeta (t0+h*s)) (deta (t0+h*s))) := by
  have hq := (actual_d_gauge_stage g (v (t0+h*s)) beta eta (t0+h*s)
    (dbeta (t0+h*s)) (deta (t0+h*s)) hg hb he hbeta heta hD).2.1
  simpa only [pathBody,originalUpperBodyCoordinates_velocity] using
    normalizedUpperPath_body (gaugedPath g beta eta) _ t0 h sx sy sz s hsx hsy hsz hq

theorem parabolic_body_formula
    (g v : ℝ → Fin 6 → ℝ) (beta eta dbeta deta : ℝ → ℝ)
    (t0 H theta w s : ℝ) (hH : 0 < H) (htheta : 0 < theta) (hw : 0 < w)
    (hg : HasDerivAt g (v (t0+theta*H*s)) (t0+theta*H*s))
    (hb : HasDerivAt beta (dbeta (t0+theta*H*s)) (t0+theta*H*s))
    (he : HasDerivAt eta (deta (t0+theta*H*s)) (t0+theta*H*s))
    (hbeta : beta (t0+theta*H*s) =
      originalAffineBodyCoordinates (g (t0+theta*H*s)) (v (t0+theta*H*s)) 1)
    (heta : eta (t0+theta*H*s) =
      originalAffineBodyCoordinates (g (t0+theta*H*s)) (v (t0+theta*H*s)) 4)
    (hD : originalAffineBodyCoordinates (g (t0+theta*H*s)) (v (t0+theta*H*s)) 3 = 1) :
    pathBody (parabolicPath g beta eta t0 H theta w) s =
      ![theta^2*H*w*correctedA g v dbeta (t0+theta*H*s),0,
        mixedRate g v (t0+theta*H*s),1,0,H*correctedF g v deta (t0+theta*H*s)/w] := by
  rw [parabolicPath,normalized_gauge_body g v beta eta dbeta deta t0 (theta*H)
    (theta*H) (theta^2*H*w) (theta*w) s (by positivity) (by positivity) (by positivity)
    hg hb he hbeta heta hD]
  ext i
  fin_cases i <;> simp [normalizedBodyRates,gaugeBodyRates,correctedA,correctedF,mixedRate]
    <;> field_simp <;> ring

theorem cubic_body_formula
    (g v : ℝ → Fin 6 → ℝ) (beta eta dbeta deta : ℝ → ℝ)
    (t0 H theta u w s : ℝ) (hH : 0 < H) (htheta : 0 < theta) (hu : 0 < u) (hw : 0 < w)
    (hg : HasDerivAt g (v (t0+theta*H*s)) (t0+theta*H*s))
    (hb : HasDerivAt beta (dbeta (t0+theta*H*s)) (t0+theta*H*s))
    (he : HasDerivAt eta (deta (t0+theta*H*s)) (t0+theta*H*s))
    (hbeta : beta (t0+theta*H*s) =
      originalAffineBodyCoordinates (g (t0+theta*H*s)) (v (t0+theta*H*s)) 1)
    (heta : eta (t0+theta*H*s) =
      originalAffineBodyCoordinates (g (t0+theta*H*s)) (v (t0+theta*H*s)) 4)
    (hD : originalAffineBodyCoordinates (g (t0+theta*H*s)) (v (t0+theta*H*s)) 3 = 1) :
    pathBody (cubicPath g beta eta t0 H theta u w) s =
      ![H*correctedA g v dbeta (t0+theta*H*s)/u,0,
        mixedRate g v (t0+theta*H*s)/(theta^2*u*w),1,0,
        H*correctedF g v deta (t0+theta*H*s)/w] := by
  rw [cubicPath,normalized_gauge_body g v beta eta dbeta deta t0 (theta*H)
    (theta^3*H*u*w) (theta^2*H*w) (theta*w) s
    (by positivity) (by positivity) (by positivity) hg hb he hbeta heta hD]
  ext i
  fin_cases i <;> simp [normalizedBodyRates,gaugeBodyRates,correctedA,correctedF,mixedRate]
    <;> field_simp <;> ring

theorem parabolicPath_matrix (g : ℝ → Fin 6 → ℝ) (beta eta : ℝ → ℝ)
    (t0 H theta w s : ℝ) (hH : 0 < H) (htheta : 0 < theta) (hw : 0 < w) :
    originalAffineHomogeneousMatrix (parabolicPath g beta eta t0 H theta w s) =
      normalizedMatrixPath (fun t => originalAffineHomogeneousMatrix (gaugedPath g beta eta t))
        t0 (theta*H) (theta*H) (theta^2*H*w) (theta*w) s := by
  exact normalizedUpperPath_matrix _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) s

theorem cubicPath_matrix (g : ℝ → Fin 6 → ℝ) (beta eta : ℝ → ℝ)
    (t0 H theta u w s : ℝ) (hH : 0 < H) (htheta : 0 < theta) (hu : 0 < u) (hw : 0 < w) :
    originalAffineHomogeneousMatrix (cubicPath g beta eta t0 H theta u w s) =
      normalizedMatrixPath (fun t => originalAffineHomogeneousMatrix (gaugedPath g beta eta t))
        t0 (theta*H) (theta^3*H*u*w) (theta^2*H*w) (theta*w) s := by
  exact normalizedUpperPath_matrix _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) s

private theorem actual_raw_sup_bounds
    (g v : ℝ → Fin 6 → ℝ) (dbeta deta : ℝ → ℝ) (S : Set ℝ) (t0 H B Db De : ℝ)
    (ht0 : t0 ∈ S) (hH : 0 ≤ H)
    (hbody : ∀ t ∈ S, ∀ i : Fin 6, |originalAffineBodyCoordinates (g t) (v t) i| ≤ B)
    (hdb : ∀ t ∈ S, |dbeta t| ≤ Db) (hde : ∀ t ∈ S, |deta t| ≤ De) :
    0 ≤ rawU H S g v dbeta ∧ 0 ≤ rawW H S g v deta ∧
      ∀ t ∈ S, H*|correctedA g v dbeta t| ≤ rawU H S g v dbeta ∧
        H*|correctedF g v deta t| ≤ rawW H S g v deta := by
  have hbA : BddAbove ((fun t => |correctedA g v dbeta t|) '' S) := by
    refine ⟨B+Db,?_⟩
    rintro _ ⟨t,ht,rfl⟩
    exact (abs_add _ _).trans (add_le_add (hbody t ht 0) (hdb t ht))
  have hbF : BddAbove ((fun t => |correctedF g v deta t|) '' S) := by
    refine ⟨B+De,?_⟩
    rintro _ ⟨t,ht,rfl⟩
    exact (abs_sub _ _).trans (add_le_add (hbody t ht 5) (hde t ht))
  have hA (t : ℝ) (ht : t ∈ S) : |correctedA g v dbeta t| ≤ rateSup S (correctedA g v dbeta) :=
    le_csSup hbA ⟨t,ht,rfl⟩
  have hF (t : ℝ) (ht : t ∈ S) : |correctedF g v deta t| ≤ rateSup S (correctedF g v deta) :=
    le_csSup hbF ⟨t,ht,rfl⟩
  refine ⟨mul_nonneg hH ((abs_nonneg _).trans (hA t0 ht0)),
    mul_nonneg hH ((abs_nonneg _).trans (hF t0 ht0)),?_⟩
  intro t ht
  exact ⟨mul_le_mul_of_nonneg_left (hA t ht) hH,mul_le_mul_of_nonneg_left (hF t ht) hH⟩

private theorem mixedRate_abs_le (g v : ℝ → Fin 6 → ℝ) (t B : ℝ) (hB : 0 ≤ B)
    (hbody : ∀ i : Fin 6, |originalAffineBodyCoordinates (g t) (v t) i| ≤ B) :
    |mixedRate g v t| ≤ B+B^2 := by
  have hm : |originalAffineBodyCoordinates (g t) (v t) 1 *
      originalAffineBodyCoordinates (g t) (v t) 4| ≤ B^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul (hbody 1) (hbody 4) (abs_nonneg _) hB
  exact (abs_sub _ _).trans (add_le_add (hbody 2) hm)

/-- Exact actual residual bounds on the same source set as the raw suprema.
The zero raw first-shear case is allowed in the parabolic branch. -/
theorem actual_residual_bounds
    (g v : ℝ → Fin 6 → ℝ) (beta eta dbeta deta : ℝ → ℝ)
    (S : Set ℝ) (t0 H P C Db De theta s : ℝ)
    (_hS : Convex ℝ S) (ht0 : t0 ∈ S) (hH : 1 ≤ H) (hP : 2 ≤ P)
    (_hspan : ∀ t ∈ S, |t-t0| ≤ H) (htheta : 0 < theta) (_htheta1 : theta < 1)
    (hx : t0+theta*H*s ∈ S)
    (hg : ∀ t ∈ S, HasDerivAt g (v t) t)
    (hb : ∀ t ∈ S, HasDerivAt beta (dbeta t) t)
    (he : ∀ t ∈ S, HasDerivAt eta (deta t) t)
    (hbeta : ∀ t ∈ S, beta t = originalAffineBodyCoordinates (g t) (v t) 1)
    (heta : ∀ t ∈ S, eta t = originalAffineBodyCoordinates (g t) (v t) 4)
    (hD : ∀ t ∈ S, originalAffineBodyCoordinates (g t) (v t) 3 = 1)
    (hbody : ∀ t ∈ S, ∀ i : Fin 6, |originalAffineBodyCoordinates (g t) (v t) i| ≤ P^C)
    (hdb : ∀ t ∈ S, |dbeta t| ≤ Db) (hde : ∀ t ∈ S, |deta t| ≤ De) :
    let u := rawU H S g v dbeta
    let w := rawW H S g v deta
    0 ≤ u ∧ 0 ≤ w ∧
    (0 < w → |pathBody (parabolicPath g beta eta t0 H theta w) s 0| ≤ theta^2*u*w) ∧
    (0 < u*w → |pathBody (cubicPath g beta eta t0 H theta u w) s 2| ≤
      (P^C+(P^C)^2)/(theta^2*u*w)) := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hB0 : 0 ≤ P^C := Real.rpow_nonneg (by linarith) _
  obtain ⟨hu,hw,hraw⟩ := actual_raw_sup_bounds g v dbeta deta S t0 H (P^C) Db De
    ht0 hH0 hbody hdb hde
  refine ⟨hu,hw,?_,?_⟩
  · intro hwpos
    rw [parabolic_body_formula g v beta eta dbeta deta t0 H theta _ s hHpos htheta hwpos
      (hg _ hx) (hb _ hx) (he _ hx) (hbeta _ hx) (heta _ hx) (hD _ hx)]
    simp only [Matrix.cons_val_zero]
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ theta^2*H*rawW H S g v deta)]
    have hh := mul_le_mul_of_nonneg_left (hraw _ hx).1
      (by positivity : 0 ≤ theta^2*rawW H S g v deta)
    nlinarith only [hh]
  · intro hprod
    have hupos : 0 < rawU H S g v dbeta := pos_of_mul_pos_left hprod hw
    have hwpos : 0 < rawW H S g v deta := pos_of_mul_pos_right hprod hu
    rw [cubic_body_formula g v beta eta dbeta deta t0 H theta _ _ s hHpos htheta hupos hwpos
      (hg _ hx) (hb _ hx) (he _ hx) (hbeta _ hx) (heta _ hx) (hD _ hx)]
    simp only [Matrix.cons_val,Matrix.cons_val_zero]
    rw [abs_div,abs_of_pos (by positivity : 0 < theta^2*rawU H S g v dbeta*rawW H S g v deta)]
    exact div_le_div_of_nonneg_right (mixedRate_abs_le g v _ _ hB0 (hbody _ hx)) (by positivity)

/-- A fixed short fraction is absorbed into a single exponent chosen before P. -/
theorem fixed_theta_conditioning (theta : ℝ) (_htheta : 0 < theta) :
    ∃ N : ℕ, ∀ P : ℝ, 2 ≤ P → (theta^2)⁻¹ ≤ P^(N:ℝ) := by
  have hn (n : ℕ) : (n:ℝ)+1 ≤ (2:ℝ)^n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ, Nat.cast_succ]
      have hn0 : 0 ≤ (n:ℝ) := by positivity
      nlinarith only [ih, hn0]
  obtain ⟨N,hN⟩ := exists_nat_gt ((theta^2)⁻¹)
  refine ⟨N,?_⟩
  intro P hP
  rw [Real.rpow_natCast]
  calc
    (theta^2)⁻¹ ≤ (N:ℝ)+1 := by linarith
    _ ≤ (2:ℝ)^N := hn N
    _ ≤ P^N := pow_le_pow_left₀ (by norm_num) hP N

theorem mixed_rate_conditioning_power (P C : ℝ) (hP : 2 ≤ P) (hB : 1 ≤ P^C) :
    P^C+(P^C)^2 ≤ P^(2*C+1) := by
  have hPpos : 0 < P := by linarith
  have hB0 : 0 ≤ P^C := zero_le_one.trans hB
  have hBB : P^C ≤ (P^C)^2 := by
    simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hB hB0
  have hscale := mul_le_mul_of_nonneg_left hP (sq_nonneg (P^C))
  rw [show 2*C+1 = C*2+1 by ring, Real.rpow_add hPpos,
    Real.rpow_mul hPpos.le, Real.rpow_two, Real.rpow_one]
  nlinarith only [hBB,hscale]

/-- The conditioning factor is used only after theta has been fixed. -/
theorem residual_bound_conditioned (P C theta z r : ℝ) (N : ℕ)
    (hP : 2 ≤ P) (hB : 1 ≤ P^C) (hz : 0 < z)
    (hfactor : (theta^2)⁻¹ ≤ P^(N:ℝ))
    (hr : |r| ≤ (P^C+(P^C)^2)/(theta^2*z)) :
    |r| ≤ P^(2*C+1+(N:ℝ))/z := by
  have hPpos : 0 < P := by linarith
  have hm := mul_le_mul (mixed_rate_conditioning_power P C hP hB) hfactor
    (inv_nonneg.mpr (sq_nonneg theta)) (Real.rpow_pos_of_pos hPpos (2*C+1)).le
  calc
    |r| ≤ (P^C+(P^C)^2)/(theta^2*z) := hr
    _ = ((P^C+(P^C)^2)*(theta^2)⁻¹)/z := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (P^(2*C+1)*P^(N:ℝ))/z := div_le_div_of_nonneg_right hm hz.le
    _ = P^(2*C+1+(N:ℝ))/z := by
      rw [Real.rpow_add hPpos (2*C+1) (N:ℝ)]

theorem residual_bound_of_power_dominance (P D E z r : ℝ)
    (hP : 0 < P) (_hz : 0 < z) (hr : |r| ≤ P^D/z)
    (hdominance : P^(D+E) ≤ z) : |r| ≤ P^(-E) := by
  calc
    |r| ≤ P^D/z := hr
    _ ≤ P^D/P^(D+E) := div_le_div_of_nonneg_left
      (Real.rpow_pos_of_pos hP D).le (Real.rpow_pos_of_pos hP (D+E)) hdominance
    _ = P^(-E) := by
      rw [← Real.rpow_sub hP]
      congr 1
      ring

theorem residual_bound_of_exact_threshold (theta z eps M r : ℝ)
    (htheta : 0 < theta) (hz : 0 < z) (heps : 0 < eps)
    (hr : |r| ≤ M/(theta^2*z))
    (hdominance : M/(theta^2*eps) ≤ z) : |r| ≤ eps := by
  have htheta2 : 0 < theta^2 := sq_pos_of_pos htheta
  apply hr.trans
  apply (div_le_iff₀ (mul_pos htheta2 hz)).mpr
  have hm := (div_le_iff₀ (mul_pos htheta2 heps)).mp hdominance
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hm

/-- The integer exponent depends only on the fixed sampling fraction.
All subsequent conditioning variables and the desired power E are quantified
after that choice. The original unmaximized product is the scalar z. -/
theorem fixed_theta_residual_conditioning (theta : ℝ) (htheta : 0 < theta) :
    ∃ N : ℕ, ∀ P C z r E : ℝ, 2 ≤ P → 1 ≤ P^C → 0 < z →
      |r| ≤ (P^C+(P^C)^2)/(theta^2*z) →
      |r| ≤ P^(2*C+1+(N:ℝ))/z ∧
      (P^(2*C+1+(N:ℝ)+E) ≤ z → |r| ≤ P^(-E)) := by
  obtain ⟨N,hN⟩ := fixed_theta_conditioning theta htheta
  refine ⟨N,?_⟩
  intro P C z r E hP hB hz hr
  have hcond := residual_bound_conditioned P C theta z r N hP hB hz (hN P hP) hr
  refine ⟨hcond,?_⟩
  intro hdominance
  exact residual_bound_of_power_dominance P (2*C+1+(N:ℝ)) E z r
    (by linarith) hz hcond hdominance


/-- The complete selected error-coefficient stage. A fixed theta determines
one exponent N before P, the interval length, path, raw amplitudes and point.
Both exact and conditioned thresholds act on actual normalized path bodies.
The parabolic conclusion controls only its residual, not model covering. -/
theorem actual_parabolic_cubic_residual_stage (theta : ℝ)
    (htheta : 0 < theta) (htheta1 : theta < 1) :
    ∃ N : ℕ,
    ∀ (g v : ℝ → Fin 6 → ℝ) (beta eta dbeta deta : ℝ → ℝ)
      (S : Set ℝ) (t0 H P C Db De s : ℝ),
    Convex ℝ S → t0 ∈ S → 1 ≤ H → 2 ≤ P →
    (∀ t ∈ S, |t-t0| ≤ H) → t0+theta*H*s ∈ S →
    (∀ t ∈ S, HasDerivAt g (v t) t) →
    (∀ t ∈ S, HasDerivAt beta (dbeta t) t) →
    (∀ t ∈ S, HasDerivAt eta (deta t) t) →
    (∀ t ∈ S, beta t = originalAffineBodyCoordinates (g t) (v t) 1) →
    (∀ t ∈ S, eta t = originalAffineBodyCoordinates (g t) (v t) 4) →
    (∀ t ∈ S, originalAffineBodyCoordinates (g t) (v t) 3 = 1) →
    (∀ t ∈ S, ∀ i : Fin 6, |originalAffineBodyCoordinates (g t) (v t) i| ≤ P^C) →
    (∀ t ∈ S, |dbeta t| ≤ Db) → (∀ t ∈ S, |deta t| ≤ De) →
    let u := rawU H S g v dbeta
    let w := rawW H S g v deta
    0 ≤ u ∧ 0 ≤ w ∧
    (0 < w →
      |pathBody (parabolicPath g beta eta t0 H theta w) s 0| ≤ theta^2*u*w ∧
      ∀ K eps : ℝ, u*w ≤ K → theta^2*K ≤ eps →
        |pathBody (parabolicPath g beta eta t0 H theta w) s 0| ≤ eps) ∧
    (0 < u*w →
      |pathBody (cubicPath g beta eta t0 H theta u w) s 2| ≤
        (P^C+(P^C)^2)/(theta^2*u*w) ∧
      |pathBody (cubicPath g beta eta t0 H theta u w) s 2| ≤
        P^(2*C+1+(N:ℝ))/(u*w)) ∧
    (∀ eps : ℝ, 0 < eps → (P^C+(P^C)^2)/(theta^2*eps) ≤ u*w →
      |pathBody (cubicPath g beta eta t0 H theta u w) s 2| ≤ eps) ∧
    (∀ E : ℝ, P^(2*C+1+(N:ℝ)+E) ≤ u*w →
      |pathBody (cubicPath g beta eta t0 H theta u w) s 2| ≤ P^(-E)) := by
  obtain ⟨N,hN⟩ := fixed_theta_conditioning theta htheta
  refine ⟨N,?_⟩
  intro g v beta eta dbeta deta S t0 H P C Db De s hS ht0 hH hP
    hspan hx hg hb he hbeta heta hD hbody hdb hde
  have hraw := actual_residual_bounds g v beta eta dbeta deta S t0 H P C Db De theta s
    hS ht0 hH hP hspan htheta htheta1 hx hg hb he hbeta heta hD hbody hdb hde
  have hB1 : 1 ≤ P^C := by simpa [hD t0 ht0] using hbody t0 ht0 3
  have hMpos : 0 < P^C+(P^C)^2 := by nlinarith only [hB1,sq_nonneg (P^C)]
  have hPpos : 0 < P := by linarith
  have hcond (hz : 0 < rawU H S g v dbeta*rawW H S g v deta) :
      |pathBody (cubicPath g beta eta t0 H theta
        (rawU H S g v dbeta) (rawW H S g v deta)) s 2| ≤
        P^(2*C+1+(N:ℝ))/(rawU H S g v dbeta*rawW H S g v deta) := by
    apply residual_bound_conditioned P C theta _ _ N hP hB1 hz (hN P hP)
    simpa only [mul_assoc] using hraw.2.2.2 hz
  refine ⟨hraw.1,hraw.2.1,?_,?_,?_,?_⟩
  · intro hw
    refine ⟨hraw.2.2.1 hw,?_⟩
    intro K eps hK heps
    have hh := mul_le_mul_of_nonneg_left hK (sq_nonneg theta)
    nlinarith only [hraw.2.2.1 hw,hh,heps]
  · intro hz
    exact ⟨hraw.2.2.2 hz,hcond hz⟩
  · intro eps heps hthreshold
    have hz : 0 < rawU H S g v dbeta*rawW H S g v deta :=
      (div_pos hMpos (mul_pos (sq_pos_of_pos htheta) heps)).trans_le hthreshold
    apply residual_bound_of_exact_threshold theta _ eps _ _ htheta hz heps
    · simpa only [mul_assoc] using hraw.2.2.2 hz
    · exact hthreshold
  · intro E hthreshold
    have hz : 0 < rawU H S g v dbeta*rawW H S g v deta :=
      (Real.rpow_pos_of_pos hPpos _).trans_le hthreshold
    exact residual_bound_of_power_dominance P (2*C+1+(N:ℝ)) E _ _ hPpos hz
      (hcond hz) hthreshold

end PaperI.DComparisonCoefficients
