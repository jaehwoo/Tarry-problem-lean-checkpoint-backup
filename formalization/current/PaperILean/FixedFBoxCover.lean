import PaperILean.FixedFSliceRounding
import PaperILean.IntegerPointBoxes
import PaperILean.OriginalFBox

/-! I1574: deterministic five-dimensional covers of the original fixed-f box.
The lattice is rounded in the triangular group coordinates. Its half-open
right cube patches are the disjoint slice patches of I1468-I1476. -/

noncomputable section
open scoped BigOperators
namespace PaperI.FixedFBoxCover
open FixedFSliceRounding

/-- The five source widths on a fixed original f-slice. -/
def sliceWeight (H u : ℝ) (i : Fin 5) : ℝ :=
  OriginalFBox.boxWeight H u i.castSucc

def SliceBoxBound (x : Fin 6 → ℝ) (K H u : ℝ) : Prop :=
  ∀ i : Fin 5, |x i.castSucc| ≤ K * sliceWeight H u i

/-- All possible lattice labels, fixed before a point or phase is chosen. -/
def catalog (H u K eps : ℝ) : Finset (Fin 5 → ℤ) :=
  Fintype.piFinset fun i => integerIntervalAround 0 ((2*K+2)*sliceWeight H u i/eps)

def fixedFNet (H u K eps F : ℝ) : Finset (Fin 6 → ℝ) := by
  classical
  exact (catalog H u K eps).image (latticeCenter eps F)

theorem sliceWeight_ge_one (H u : ℝ) (hH : 1 ≤ H) (i : Fin 5) :
    1 ≤ sliceWeight H u i := by
  have hB : 1 ≤ max H u := hH.trans (le_max_left _ _)
  have hHB : 1 ≤ H * max H u := one_le_mul_of_one_le_of_one_le hH hB
  fin_cases i <;>
    simp only [sliceWeight, OriginalFBox.boxWeight, Fin.castSucc_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  · exact hH
  · exact hB
  · exact hHB
  · exact le_max_left _ _
  · exact hB

private theorem rounded_bound (x w K eps : ℝ)
    (hw : 1 ≤ w) (hK : 1 ≤ K) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hx : |x| ≤ K*w) : |meshRound eps x| ≤ (K+1)*w := by
  have hew : eps ≤ w := heps1.trans hw
  calc
    _ ≤ |x|+eps := abs_meshRound_le eps x heps
    _ ≤ K*w+w := add_le_add hx hew
    _ = _ := by ring

private theorem sheared_rounded_bound (x A y w W K eps : ℝ)
    (hw : 0 ≤ w) (hW : 1 ≤ W) (hwW : w ≤ W) (hK : 1 ≤ K)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hx : |x| ≤ K*W) (hA : |A| ≤ (K+1)*w) (hy : |y| ≤ eps) :
    |meshRound eps (x-A*y)| ≤ (2*K+2)*W := by
  have hK1 : 0 ≤ K+1 := by linarith
  have hAy : |A*y| ≤ (K+1)*W := by
    calc
      _ = |A| * |y| := abs_mul _ _
      _ ≤ ((K+1)*w)*1 := mul_le_mul hA (hy.trans heps1)
        (abs_nonneg _) (mul_nonneg hK1 hw)
      _ ≤ (K+1)*W := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hwW hK1
  calc
    _ ≤ |x-A*y|+eps := abs_meshRound_le eps (x-A*y) heps
    _ ≤ (|x|+|A*y|)+eps := add_le_add_right (abs_sub _ _) _
    _ ≤ (K*W+(K+1)*W)+W := add_le_add (add_le_add hx hAy) (heps1.trans hW)
    _ = _ := by ring

/-- Triangular rounding stays in an explicitly enlarged source box. -/
theorem rounded_center_bound (H u K eps F : ℝ) (x : Fin 6 → ℝ)
    (hH : 1 ≤ H) (hK : 1 ≤ K) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hx : SliceBoxBound x K H u) :
    ∀ i : Fin 5,
      |latticeCenter eps F (triIndex eps x) i.castSucc| ≤
        (2*K+2)*sliceWeight H u i := by
  have hH0 : 0 ≤ H := by linarith
  have hB : 1 ≤ max H u := hH.trans (le_max_left _ _)
  have hHB : 1 ≤ H*max H u := one_le_mul_of_one_le_of_one_le hH hB
  have hHHB : H ≤ H*max H u := le_mul_of_one_le_right hH0 hB
  have ha : |meshRound eps (x 0)| ≤ (K+1)*H :=
    rounded_bound (x 0) H K eps hH hK heps heps1 (hx 0)
  have hd : |x 3-meshRound eps (x 3)| ≤ eps := by
    rw [abs_of_nonneg (meshRound_residual eps (x 3) heps).1]
    exact (meshRound_residual eps (x 3) heps).2.le
  have he : |x 4-meshRound eps (x 4)| ≤ eps := by
    rw [abs_of_nonneg (meshRound_residual eps (x 4) heps).1]
    exact (meshRound_residual eps (x 4) heps).2.le
  have hb := sheared_rounded_bound (x 1) (meshRound eps (x 0))
    (x 3-meshRound eps (x 3)) H (max H u) K eps hH0 hB
    (le_max_left _ _) hK heps heps1 (hx 1) ha hd
  have hc := sheared_rounded_bound (x 2) (meshRound eps (x 0))
    (x 4-meshRound eps (x 4)) H (H*max H u) K eps hH0 hHB
    hHHB hK heps heps1 (hx 2) ha he
  have hs (i : Fin 5) :
      |meshRound eps (x i.castSucc)| ≤ (2*K+2)*sliceWeight H u i := by
    have hh := rounded_bound (x i.castSucc) (sliceWeight H u i) K eps
      (sliceWeight_ge_one H u hH i) hK heps heps1 (hx i)
    have hw0 : 0 ≤ sliceWeight H u i := (zero_le_one.trans (sliceWeight_ge_one H u hH i))
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : K+1 ≤ 2*K+2) hw0)
  intro i
  rw [latticeCenter_triIndex]
  fin_cases i
  · exact hs 0
  · exact hb
  · exact hc
  · exact hs 3
  · exact hs 4

theorem triIndex_mem_catalog (H u K eps F : ℝ) (x : Fin 6 → ℝ)
    (hH : 1 ≤ H) (hK : 1 ≤ K) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hx : SliceBoxBound x K H u) : triIndex eps x ∈ catalog H u K eps := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply mem_integerIntervalAround_of_abs_le
  simp only [sub_zero]
  apply (le_div_iff₀ heps).mpr
  have hh := rounded_center_bound H u K eps F x hH hK heps heps1 hx i
  have heq : latticeCenter eps F (triIndex eps x) i.castSucc =
      eps * ((triIndex eps x i : ℤ) : ℝ) := by
    fin_cases i <;> simp [latticeCenter]
  rw [heq, abs_mul, abs_of_pos heps] at hh
  simpa only [mul_comm] using hh

private theorem interval_card_bound (w K eps : ℝ)
    (hw : 1 ≤ w) (hK : 1 ≤ K) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ((integerIntervalAround 0 ((2*K+2)*w/eps)).card : ℝ) ≤ (10*K/eps)*w := by
  have hw0 : 0 ≤ w := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hr : 0 ≤ (2*K+2)*w/eps := div_nonneg (mul_nonneg (by linarith) hw0) heps.le
  have hh := integerIntervalAround_card_le 0 ((2*K+2)*w/eps) hr
  have hKw : w ≤ K*w := le_mul_of_one_le_left hw0 hK
  have hew : eps ≤ w := heps1.trans hw
  apply hh.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ heps).mpr
  calc
    (2*((2*K+2)*w/eps)+2)*eps = 2*((2*K+2)*w)+2*eps := by
      field_simp
    _ ≤ 10*K*w := by nlinarith only [hKw,hew]

theorem catalog_card_le (H u K eps : ℝ)
    (hH : 1 ≤ H) (hK : 1 ≤ K) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ((catalog H u K eps).card : ℝ) ≤
      (10*K/eps)^5*H^2*(max H u)^3*max 1 (u/H) := by
  change (((Fintype.piFinset fun i : Fin 5 =>
    integerIntervalAround 0 ((2*K+2)*sliceWeight H u i/eps)).card : ℕ) : ℝ) ≤ _
  rw [Fintype.card_piFinset, Nat.cast_prod]
  calc
    (∏ i : Fin 5, ((integerIntervalAround 0 ((2*K+2)*sliceWeight H u i/eps)).card : ℝ)) ≤
        ∏ i : Fin 5, (10*K/eps)*sliceWeight H u i :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => interval_card_bound (sliceWeight H u i) K eps
          (sliceWeight_ge_one H u hH i) hK heps heps1)
    _ = _ := by
      simp [Fin.prod_univ_succ, sliceWeight, OriginalFBox.boxWeight]
      ring

theorem fixedFNet_card_le (H u K eps F : ℝ)
    (hH : 1 ≤ H) (hK : 1 ≤ K) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ((fixedFNet H u K eps F).card : ℝ) ≤
      (10*K/eps)^5*H^2*(max H u)^3*max 1 (u/H) := by
  classical
  exact (Nat.cast_le.mpr (Finset.card_image_le)).trans
    (catalog_card_le H u K eps hH hK heps heps1)

/-- Complete geometric fixed-f covering stage, with no restriction on the
common f-value and no assumed covering or phase-selection conclusion. -/
theorem fixed_f_box_cover (H u K eps F : ℝ)
    (hH : 1 ≤ H) (hK : 1 ≤ K) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ((fixedFNet H u K eps F).card : ℝ) ≤
        (10*K/eps)^5*H^2*(max H u)^3*max 1 (u/H) ∧
      ∀ x : Fin 6 → ℝ, x 5 = F → SliceBoxBound x K H u →
        ∃ c ∈ fixedFNet H u K eps F, c 5 = F ∧
          InRightCube eps (originalUpperRelativeFrame c x) := by
  classical
  refine ⟨fixedFNet_card_le H u K eps F hH hK heps heps1, ?_⟩
  intro x hf hx
  refine ⟨latticeCenter eps F (triIndex eps x), ?_, ?_,
    rounded_relative_mem eps F x heps hf⟩
  · exact Finset.mem_image.mpr ⟨triIndex eps x,
      triIndex_mem_catalog H u K eps F x hH hK heps heps1 hx, rfl⟩
  · exact latticeCenter_fixed_f eps F (triIndex eps x)

end PaperI.FixedFBoxCover
