import PaperILean.TensorContractionBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Exact square-minor volume and coordinate bounds used by the complete
fixed-net coefficient envelope at I1387-I1395. The determinant uses every
input coordinate. No measurable-subset or chosen-phase hypothesis is needed. -/
noncomputable section
open scoped BigOperators ENNReal
open Set MeasureTheory
namespace PaperI.SampleMinorVolume

/-- A single coordinate is bounded by the full Euclidean coordinate norm. -/
theorem abs_le_coordinateL2Norm {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (i : ι) : |v i| ≤ coordinateL2Norm v := by
  classical
  have hs : (v i)^2 ≤ ∑ j, (v j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  rw [← coordinateL2Norm_sq] at hs
  nlinarith [coordinateL2Norm_nonneg v, abs_nonneg (v i), sq_abs (v i)]

/-- The inverse determinant controls the entire inverse image of an output
box, also in dimension zero. The positive determinant threshold is essential. -/
theorem linear_box_volume_le {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (Δ W : ℝ)
    (hΔ : 0 < Δ) (hdet : Δ ≤ |LinearMap.det f|) (hW : 0 ≤ W) :
    volume {x | ∀ i, |f x i| ≤ W} ≤
      ENNReal.ofReal (Δ⁻¹ * (2*W)^Fintype.card ι) := by
  classical
  let B : Set (ι → ℝ) := Icc (fun _ => -W) (fun _ => W)
  have hf : LinearMap.det f ≠ 0 := by
    have hp : 0 < |LinearMap.det f| := hΔ.trans_le hdet
    exact abs_pos.mp hp
  have he : {x | ∀ i, |f x i| ≤ W} = f ⁻¹' B := by
    ext x
    simp [B, abs_le, Pi.le_def, forall_and]
  have hB : volume B = ENNReal.ofReal ((2*W)^Fintype.card ι) := by
    rw [show B = Icc (fun _ : ι => -W) (fun _ => W) from rfl,
      Real.volume_Icc_pi]
    simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ,
      ← ENNReal.ofReal_pow (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hW)]
  have hm : volume (f ⁻¹' B) =
      ENNReal.ofReal (|LinearMap.det f|⁻¹) * volume B := by
    rw [← Measure.map_apply f.continuous_of_finiteDimensional.measurable
      (show MeasurableSet B from measurableSet_Icc),
      Real.map_linearMap_volume_pi_eq_smul_volume_pi hf,
      Measure.smul_apply, smul_eq_mul, abs_inv]
  rw [he, hm, hB]
  calc
    ENNReal.ofReal (|LinearMap.det f|⁻¹) * ENNReal.ofReal ((2*W)^Fintype.card ι)
      ≤ ENNReal.ofReal (Δ⁻¹) * ENNReal.ofReal ((2*W)^Fintype.card ι) :=
        mul_le_mul_right' (ENNReal.ofReal_le_ofReal (inv_anti₀ hΔ hdet)) _
    _ = ENNReal.ofReal (Δ⁻¹ * (2*W)^Fintype.card ι) :=
      (ENNReal.ofReal_mul (inv_nonneg.mpr hΔ.le)).symm

/-- A fixed coefficient-operator constant and all stated polynomial windows
are absorbed uniformly before the scale P is supplied. Negative source
exponents and the zero-dimensional power n=0 are retained. -/
theorem polynomial_box_factor_le (k n : ℕ) (Cbase Ct Cm Cw : ℝ)
    (hC : 1 ≤ Cbase) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ P : ℝ, 2 ≤ P →
      (2*(P^Cm)*(Cbase*(3*(1+P^Ct))^(2*k))*
        (Cbase*(3*(1+P^Ct))^(2*k))*(P^Cw))^n ≤ P^E := by
  obtain ⟨b,_,hb⟩ := exists_nat_pow_near hC (by norm_num : (1 : ℝ) < 2)
  let eK : ℝ := (b+1 : ℕ) + (3 + max Ct 0)*(2*k : ℕ)
  let e : ℝ := 1 + max Cm 0 + eK + eK + max Cw 0
  have heK : 0 ≤ eK := by dsimp [eK]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  refine ⟨e*(n : ℝ), mul_nonneg he (Nat.cast_nonneg n), ?_⟩
  intro P hP
  have hPpos : 0 < P := by linarith
  have hP0 : 0 ≤ P := hPpos.le
  have hP1 : 1 ≤ P := by linarith
  have hbase : Cbase ≤ P^((b+1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact hb.le.trans (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hP (b+1))
  have hCt : P^Ct ≤ P^(max Ct 0) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (le_max_left _ _)
  have hCm : P^Cm ≤ P^(max Cm 0) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (le_max_left _ _)
  have hCw : P^Cw ≤ P^(max Cw 0) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (le_max_left _ _)
  have hone : 1 ≤ P^(max Ct 0) := Real.one_le_rpow hP1 (le_max_right _ _)
  have hsix : (6 : ℝ) ≤ P^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hP 3
    norm_num at h
    linarith
  have hsum : 3*(1+P^Ct) ≤ P^(3+max Ct 0) := by
    calc
      3*(1+P^Ct) ≤ 6*P^(max Ct 0) := by linarith
      _ ≤ P^3 * P^(max Ct 0) :=
        mul_le_mul_of_nonneg_right hsix (Real.rpow_nonneg hP0 _)
      _ = P^(3+max Ct 0) := by
        rw [← Real.rpow_natCast P 3, ← Real.rpow_add hPpos]
        norm_num
  have hK : Cbase*(3*(1+P^Ct))^(2*k) ≤ P^eK := by
    calc
      Cbase*(3*(1+P^Ct))^(2*k) ≤
          P^((b+1 : ℕ) : ℝ) * (P^(3+max Ct 0))^(2*k) :=
        mul_le_mul hbase
          (pow_le_pow_left₀ (by positivity) hsum (2*k))
          (by positivity) (by positivity)
      _ = P^eK := by
        rw [← Real.rpow_natCast (P^(3+max Ct 0)) (2*k),
          ← Real.rpow_mul hP0, ← Real.rpow_add hPpos]
  have hprod : 2*(P^Cm)*(Cbase*(3*(1+P^Ct))^(2*k))*
      (Cbase*(3*(1+P^Ct))^(2*k))*(P^Cw) ≤ P^e := by
    calc
      _ ≤ P*(P^(max Cm 0))*(P^eK)*(P^eK)*(P^(max Cw 0)) := by
        gcongr
      _ = P^e := by
        nth_rw 1 [← Real.rpow_one P]
        rw [← Real.rpow_add hPpos, ← Real.rpow_add hPpos,
          ← Real.rpow_add hPpos, ← Real.rpow_add hPpos]
  calc
    _ ≤ (P^e)^n := pow_le_pow_left₀ (by positivity) hprod n
    _ = P^(e*(n : ℝ)) := by
      rw [← Real.rpow_natCast (P^e) n, ← Real.rpow_mul hP0]

end PaperI.SampleMinorVolume
