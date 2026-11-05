import PaperILean.OriginalQuadraticGaussFrame

/-! I1305, using the model-box order from I873-I903: fix a Gauss parameter
box first. Exact forward and reverse reference frames are polynomially bounded
on the whole box, uniformly in its center and in affine/root offsets. This
does not assert persistence for a perturbed phase or admissibility windows. -/
noncomputable section
namespace PaperI

theorem originalQuadraticSchur_bound (r b v H : ℝ) (hH : 1 ≤ H)
    (hb : |b| ≤ H) (hv : |v| ≤ H) (hr : |r⁻¹| ≤ H) :
    |originalQuadraticSchur r b v| ≤ 2*H^3 := by
  have hH0 : 0 ≤ H := by linarith
  have hb2 : |b|^2 ≤ H^2 := pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hm : |b|^2*|r⁻¹| ≤ H^2*H := mul_le_mul hb2 hr (abs_nonneg _) (sq_nonneg _)
  have hpow : H ≤ H^3 := by nlinarith [mul_nonneg (by linarith : 0 ≤ H-1) (by nlinarith : 0 ≤ H^2+H)]
  calc
    _ ≤ |v|+|b^2/r| := by
      simpa [originalQuadraticSchur,sub_eq_add_neg] using (abs_add_le v (-(b^2/r)))
    _ = |v|+|b|^2*|r⁻¹| := by simp [div_eq_mul_inv,abs_mul,abs_pow]
    _ ≤ H+H^2*H := add_le_add hv hm
    _ ≤ 2*H^3 := by nlinarith [hpow]

theorem originalQuadraticRelativeVector_bound (r σ p z H M : ℝ) (hH : 1 ≤ H)
    (hM : 0 ≤ M) (hr : |r⁻¹| ≤ H) (hσ : |σ| ≤ H)
    (hp : |p| ≤ M) (hz : |z| ≤ M) :
    ‖(![p,σ*z,p^2/(2*r)+σ/2*z^2,0,p/r,z] : Fin 6 → ℝ)‖ ≤ H*(1+M)^2 := by
  have hH0 : 0 ≤ H := by linarith
  have hC0 : 0 ≤ H*(1+M)^2 := mul_nonneg hH0 (sq_nonneg _)
  have hM1 : M ≤ (1+M)^2 := by nlinarith [sq_nonneg M]
  have hM2 : M^2 ≤ (1+M)^2 := by nlinarith
  have hp2 : |p|^2 ≤ M^2 := pow_le_pow_left₀ (abs_nonneg p) hp 2
  have hz2 : |z|^2 ≤ M^2 := pow_le_pow_left₀ (abs_nonneg z) hz 2
  have hlin : M ≤ H*(1+M)^2 := hM1.trans (le_mul_of_one_le_left (sq_nonneg _) hH)
  have hmul : H*M ≤ H*(1+M)^2 := mul_le_mul_of_nonneg_left hM1 hH0
  have hquad : |p^2/(2*r)+σ/2*z^2| ≤ H*M^2 := by
    rw [show p^2/(2*r) = r⁻¹/2*p^2 by simp only [div_eq_mul_inv,mul_inv_rev]; ring]
    calc
      _ ≤ |r⁻¹/2*p^2|+|σ/2*z^2| := abs_add_le _ _
      _ = (|r⁻¹| * |p|^2+|σ| * |z|^2)/2 := by
        simp only [abs_mul,abs_div,abs_pow]
        norm_num
        ring
      _ ≤ (H*M^2+H*M^2)/2 := by gcongr
      _ = H*M^2 := by ring
  apply (pi_norm_le_iff_of_nonneg hC0).mpr
  intro i
  fin_cases i
  · simpa using hp.trans hlin
  · simpa [abs_mul] using (mul_le_mul hσ hz (abs_nonneg z) hH0).trans hmul
  · simpa using hquad.trans (mul_le_mul_of_nonneg_left hM2 hH0)
  · simpa using hC0
  · simpa [div_eq_mul_inv,abs_mul,abs_inv] using
      (mul_le_mul hp hr (abs_nonneg _) hM).trans (by simpa [mul_comm] using hmul)
  · simpa using hz.trans hlin

theorem originalQuadraticGaussFrame_box_bounds (r b v t w η H M : ℝ)
    (hr : r ≠ 0) (hH : 1 ≤ H) (hM : 0 ≤ M)
    (hri : |r⁻¹| ≤ H) (hσ : |originalQuadraticSchur r b v| ≤ H)
    (a q : Fin 2 → ℝ) (hp : |q 0-a 0| ≤ M) (hz : |q 1-a 1| ≤ M) :
    ‖originalUpperRelativeFrame (originalQuadraticGaussFrame r b v t w η a)
      (originalQuadraticGaussFrame r b v t w η q)‖ ≤ H*(1+M)^2 ∧
    ‖originalUpperRelativeFrame (originalQuadraticGaussFrame r b v t w η q)
      (originalQuadraticGaussFrame r b v t w η a)‖ ≤ H*(1+M)^2 := by
  constructor
  · rw [originalQuadraticGaussFrame_relative r b v t w η hr]
    exact originalQuadraticRelativeVector_bound r _ _ _ H M hH hM hri hσ hp hz
  · rw [originalQuadraticGaussFrame_relative r b v t w η hr]
    exact originalQuadraticRelativeVector_bound r _ _ _ H M hH hM hri hσ
      (by simpa only [abs_sub_comm] using hp) (by simpa only [abs_sub_comm] using hz)

theorem originalQuadraticGaussFrame_conditioned_box (r b v t w η H M : ℝ)
    (hr : r ≠ 0) (hH : 1 ≤ H) (hM : 0 ≤ M)
    (hb : |b| ≤ H) (hv : |v| ≤ H) (hri : |r⁻¹| ≤ H)
    (a q : Fin 2 → ℝ) (hp : |q 0-a 0| ≤ M) (hz : |q 1-a 1| ≤ M) :
    ‖originalUpperRelativeFrame (originalQuadraticGaussFrame r b v t w η a)
      (originalQuadraticGaussFrame r b v t w η q)‖ ≤ 2*H^3*(1+M)^2 ∧
    ‖originalUpperRelativeFrame (originalQuadraticGaussFrame r b v t w η q)
      (originalQuadraticGaussFrame r b v t w η a)‖ ≤ 2*H^3*(1+M)^2 := by
  have hH3 : H ≤ H^3 := by
    calc H = H^1 := by ring
         _ ≤ H^3 := pow_le_pow_right₀ hH (by decide)
  have hH0 : 0 ≤ H^3 := by positivity
  exact originalQuadraticGaussFrame_box_bounds r b v t w η (2*H^3) M hr
    (by linarith) hM (hri.trans (by linarith))
    (originalQuadraticSchur_bound r b v H hH hb hv hri) a q hp hz

theorem originalQuadraticGaussFrame_matrix_box (r b v t w η H M : ℝ)
    (hr : r ≠ 0) (hH : 1 ≤ H) (hM : 0 ≤ M)
    (hb : |b| ≤ H) (hv : |v| ≤ H) (hri : |r⁻¹| ≤ H)
    (a q : Fin 2 → ℝ) (hp : |q 0-a 0| ≤ M) (hz : |q 1-a 1| ≤ M) :
    (∀ i j : Fin 4,
      |((originalAffineHomogeneousMatrix (originalQuadraticGaussFrame r b v t w η a))⁻¹ *
        originalAffineHomogeneousMatrix (originalQuadraticGaussFrame r b v t w η q)) i j|
        ≤ 1+2*H^3*(1+M)^2) ∧
    (∀ i j : Fin 4,
      |((originalAffineHomogeneousMatrix (originalQuadraticGaussFrame r b v t w η q))⁻¹ *
        originalAffineHomogeneousMatrix (originalQuadraticGaussFrame r b v t w η a)) i j|
        ≤ 1+2*H^3*(1+M)^2) := by
  obtain ⟨hf,hi⟩ := originalQuadraticGaussFrame_conditioned_box r b v t w η H M hr hH hM hb hv hri a q hp hz
  exact originalAffineRelativeMatrix_entry_bounds _ _ _ _ hf hi

end PaperI
