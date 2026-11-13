import PaperILean.PreparationDividedDifferences
import PaperILean.OriginalPreparationSuperlevels
import PaperILean.OpenComponentIntervals

/-! Original one-variable preparation, I950: combine the actual signed
superlevel intervals with the divided-difference bound. Component counts are
separate inputs here and are supplied uniformly by OriginalPreparationSuperlevels.
No exceptional-set estimate is assumed. -/

noncomputable section
namespace PaperI
open Set MeasureTheory
open scoped ENNReal

theorem published_signed_derivative_superlevel_volume_le
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (j N K : ℕ) (f : ℝ → ℝ) (a b B δ C σ : ℝ)
    (hj : 0 < j) (hn : j ≤ N) (hab : a < b) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hC : (4*(j:ℝ)/δ)^j ≤ C) (hσ : |σ| = 1)
    (hsmooth : ContDiffOn ℝ N f (Ioo a b))
    (hamp : ∀ x ∈ Ioo a b, |f x| ≤ B)
    (hcount : Finite (ConnectedComponents
      (signedIteratedDerivativeSuperlevel f j a b (C*B/(b-a)^j) σ)) ∧
      Nat.card (ConnectedComponents
        (signedIteratedDerivativeSuperlevel f j a b (C*B/(b-a)^j) σ)) ≤ K) :
    volume (signedIteratedDerivativeSuperlevel f j a b (C*B/(b-a)^j) σ) ≤
      ENNReal.ofReal ((K:ℝ)*δ*(b-a)) := by
  letI := hcount.1
  have hL : 0 < b-a := sub_pos.mpr hab
  have hthr : (4*(j:ℝ))^j*B/(δ*(b-a))^j ≤ C*B/(b-a)^j := by
    calc
      (4*(j:ℝ))^j*B/(δ*(b-a))^j = (4*(j:ℝ)/δ)^j*B/(b-a)^j := by
        simp only [div_pow,mul_pow,div_eq_mul_inv,mul_inv_rev]
        ring
      _ ≤ C*B/(b-a)^j := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC hB) (pow_nonneg hL.le j)
  have hv := volume_open_set_le_component_count_mul
    (isOpen_signedIteratedDerivativeSuperlevel hsmooth hn (C*B/(b-a)^j) σ)
    (fun _ hx => hx.1) hcount.2 (c := δ*(b-a))
    (fun u v _ huv _ hsub => by
      have hI : Ioo u v ⊆ Ioo a b := fun x hx => (hsub hx).1
      have hs : ContDiffOn ℝ j f (Ioo u v) :=
        (hsmooth.of_le (by exact_mod_cast hn)).mono hI
      exact (published_signed_superlevel_interval_length hDD j hj f u v B δ (b-a) σ
        huv hB hδ hL hσ hs (fun x hx => hamp x (hI hx))
        (fun x hx => hthr.trans_lt (hsub hx).2)).le)
  convert hv using 1
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg K)]
  congr 1
  ring

theorem abs_derivative_superlevel_eq_signed_union
    (f : ℝ → ℝ) (j : ℕ) (a b T : ℝ) :
    {x : ℝ | x ∈ Ioo a b ∧ T < |iteratedDeriv j f x|} =
      signedIteratedDerivativeSuperlevel f j a b T 1 ∪
      signedIteratedDerivativeSuperlevel f j a b T (-1) := by
  ext x
  simp only [signedIteratedDerivativeSuperlevel,mem_setOf_eq,mem_union,one_mul,neg_one_mul,lt_abs]
  tauto

theorem published_abs_derivative_superlevel_volume_le
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (j N K : ℕ) (f : ℝ → ℝ) (a b B δ C : ℝ)
    (hj : 0 < j) (hn : j ≤ N) (hab : a < b) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hC : (4*(j:ℝ)/δ)^j ≤ C)
    (hsmooth : ContDiffOn ℝ N f (Ioo a b))
    (hamp : ∀ x ∈ Ioo a b, |f x| ≤ B)
    (hcount : ∀ σ : ℝ, |σ| = 1 →
      Finite (ConnectedComponents
        (signedIteratedDerivativeSuperlevel f j a b (C*B/(b-a)^j) σ)) ∧
      Nat.card (ConnectedComponents
        (signedIteratedDerivativeSuperlevel f j a b (C*B/(b-a)^j) σ)) ≤ K) :
    volume {x : ℝ | x ∈ Ioo a b ∧ C*B/(b-a)^j < |iteratedDeriv j f x|} ≤
      ENNReal.ofReal (2*(K:ℝ)*δ*(b-a)) := by
  have hL : 0 ≤ b-a := sub_nonneg.mpr hab.le
  rw [abs_derivative_superlevel_eq_signed_union]
  have hp := published_signed_derivative_superlevel_volume_le hDD j N K f a b B δ C 1
    hj hn hab hB hδ hC (by norm_num) hsmooth hamp (hcount 1 (by norm_num))
  have hm := published_signed_derivative_superlevel_volume_le hDD j N K f a b B δ C (-1)
    hj hn hab hB hδ hC (by norm_num) hsmooth hamp (hcount (-1) (by norm_num))
  calc
    volume (_ ∪ _) ≤ volume _ + volume _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((K:ℝ)*δ*(b-a)) + ENNReal.ofReal ((K:ℝ)*δ*(b-a)) := add_le_add hp hm
    _ = ENNReal.ofReal (2*(K:ℝ)*δ*(b-a)) := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ (K:ℝ)*δ*(b-a)) (by positivity)]
      congr 1
      ring

end PaperI
