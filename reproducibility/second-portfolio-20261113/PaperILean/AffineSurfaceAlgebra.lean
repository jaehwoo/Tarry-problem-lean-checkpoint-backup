import PaperILean.AffineSurfaceCross
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Matrix

namespace PaperI.AffineSurfaceAlgebra

open PaperI.AffineSurfaceCross

abbrev Space := PaperI.AffineSurfaceCross.Space
abbrev SecondData := Fin 2 → Fin 2 → Space

noncomputable def length (x : Space) : ℝ := Real.sqrt (dotProduct x x)

noncomputable def area (u w : Space) : ℝ := Real.sqrt (gram u w).det

noncomputable def normal (u w : Space) : Space := (area u w)⁻¹ • cross u w

noncomputable def transport (B : Matrix (Fin 3) (Fin 3) ℝ) (n : Space) : Space :=
  (B⁻¹).transpose.mulVec n

noncomputable def alpha (B : Matrix (Fin 3) (Fin 3) ℝ) (u w : Space) : ℝ :=
  length (transport B (normal u w))

noncomputable def transformedNormal (B : Matrix (Fin 3) (Fin 3) ℝ)
    (u w : Space) : Space := (alpha B u w)⁻¹ • transport B (normal u w)

def secondForm (n : Space) (H : SecondData) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => dotProduct n (H i j)

def transformedSecondData (B : Matrix (Fin 3) (Fin 3) ℝ) (H : SecondData) : SecondData :=
  fun i j => B.mulVec (H i j)

noncomputable def curvature (u w n : Space) (H : SecondData) : ℝ :=
  (secondForm n H).det / (gram u w).det

theorem dot_smul_left (a : ℝ) (x y : Space) :
    dotProduct (a • x) y = a * dotProduct x y := by
  simp [dotProduct, Fin.sum_univ_succ]
  ring

theorem dot_smul_right (a : ℝ) (x y : Space) :
    dotProduct x (a • y) = a * dotProduct x y := by
  simp [dotProduct, Fin.sum_univ_succ]
  ring

theorem length_nonneg (x : Space) : 0 ≤ length x := Real.sqrt_nonneg _

theorem length_smul (a : ℝ) (x : Space) : length (a • x) = |a| * length x := by
  unfold length
  rw [dot_smul_left, dot_smul_right]
  have heq : a * (a * dotProduct x x) = a ^ 2 * dotProduct x x := by ring
  rw [heq, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem area_eq_length (u w : Space) : area u w = length (cross u w) := by
  rw [area, length, cross_dot_self]

theorem gram_nonneg (u w : Space) : 0 ≤ (gram u w).det := by
  rw [← cross_dot_self]
  exact dot_self_nonneg _

theorem area_sq (u w : Space) : area u w ^ 2 = (gram u w).det :=
  Real.sq_sqrt (gram_nonneg u w)

theorem area_pos (u w : Space) (hreg : 0 < dotProduct (cross u w) (cross u w)) :
    0 < area u w := by
  rw [area_eq_length]
  exact Real.sqrt_pos.mpr hreg

theorem normal_unit (u w : Space) (hreg : 0 < dotProduct (cross u w) (cross u w)) :
    dotProduct (normal u w) (normal u w) = 1 := by
  have ha := area_pos u w hreg
  have hs := area_sq u w
  rw [normal, dot_smul_left, dot_smul_right, cross_dot_self]
  field_simp
  nlinarith

theorem normal_left (u w : Space) : dotProduct (normal u w) u = 0 := by
  rw [normal, dot_smul_left, cross_dot_left, mul_zero]

theorem normal_right (u w : Space) : dotProduct (normal u w) w = 0 := by
  rw [normal, dot_smul_left, cross_dot_right, mul_zero]

theorem secondForm_neg (n : Space) (H : SecondData) :
    (secondForm (-n) H).det = (secondForm n H).det := by
  simp [secondForm, Matrix.det_fin_two, dotProduct, Fin.sum_univ_succ]
  ring

theorem transport_pairing (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (n z : Space) : dotProduct (transport B n) (B.mulVec z) = dotProduct n z :=
  inverse_transpose_pairing B hB n z

theorem alpha_pos (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) (hreg : 0 < dotProduct (cross u w) (cross u w)) :
    0 < alpha B u w := by
  apply Real.sqrt_pos.mpr
  apply lt_of_le_of_ne (dot_self_nonneg _)
  intro hz
  have ht : transport B (normal u w) = 0 :=
    (dot_self_eq_zero_iff _).mp hz.symm
  have hp := transport_pairing B hB (normal u w) (normal u w)
  rw [ht, normal_unit u w hreg] at hp
  simpa using hp

theorem transformedNormal_unit (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) (hreg : 0 < dotProduct (cross u w) (cross u w)) :
    dotProduct (transformedNormal B u w) (transformedNormal B u w) = 1 := by
  have hp := alpha_pos B hB u w hreg
  have hs : alpha B u w ^ 2 = dotProduct (transport B (normal u w))
      (transport B (normal u w)) := Real.sq_sqrt (dot_self_nonneg _)
  rw [transformedNormal, dot_smul_left, dot_smul_right]
  field_simp
  nlinarith

theorem transformedNormal_left (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) : dotProduct (transformedNormal B u w) (B.mulVec u) = 0 := by
  rw [transformedNormal, dot_smul_left, transport_pairing B hB, normal_left, mul_zero]

theorem transformedNormal_right (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) : dotProduct (transformedNormal B u w) (B.mulVec w) = 0 := by
  rw [transformedNormal, dot_smul_left, transport_pairing B hB, normal_right, mul_zero]

theorem area_transformed (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) (hreg : 0 < dotProduct (cross u w) (cross u w)) :
    area (B.mulVec u) (B.mulVec w) = |B.det| * alpha B u w * area u w := by
  have ha := area_pos u w hreg
  have hn : transport B (cross u w) = area u w • transport B (normal u w) := by
    simp [transport, normal, Matrix.mulVec_smul, smul_smul, ne_of_gt ha]
  rw [area_eq_length, cross_mulVec B hB, length_smul]
  change |B.det| * length (transport B (cross u w)) = _
  rw [hn, length_smul, abs_of_pos ha]
  change |B.det| * (area u w * alpha B u w) = _
  ring

theorem gram_transformed (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) (hreg : 0 < dotProduct (cross u w) (cross u w)) :
    (gram (B.mulVec u) (B.mulVec w)).det =
      (|B.det| * alpha B u w) ^ 2 * (gram u w).det := by
  rw [← area_sq, area_transformed B hB u w hreg, mul_pow, area_sq]

theorem regular_transformed (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) (hreg : 0 < dotProduct (cross u w) (cross u w)) :
    0 < dotProduct (cross (B.mulVec u) (B.mulVec w))
      (cross (B.mulVec u) (B.mulVec w)) := by
  have hv : 0 < |B.det| := abs_pos.mpr hB
  have ha := alpha_pos B hB u w hreg
  have hg : 0 < (gram u w).det := by rw [← cross_dot_self]; exact hreg
  rw [cross_dot_self, gram_transformed B hB u w hreg]
  positivity

theorem secondForm_transformed_entry (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) (H : SecondData) (i j : Fin 2) :
    secondForm (transformedNormal B u w) (transformedSecondData B H) i j =
      secondForm (normal u w) H i j / alpha B u w := by
  dsimp [secondForm, transformedNormal, transformedSecondData]
  rw [dot_smul_left, transport_pairing B hB]
  rw [div_eq_mul_inv, mul_comm]

theorem secondForm_transformed_det (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) (H : SecondData) :
    (secondForm (transformedNormal B u w) (transformedSecondData B H)).det =
      (secondForm (normal u w) H).det / alpha B u w ^ 2 := by
  simp only [Matrix.det_fin_two, secondForm_transformed_entry B hB]
  ring

theorem curvature_transformed (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) (hreg : 0 < dotProduct (cross u w) (cross u w)) (H : SecondData) :
    curvature (B.mulVec u) (B.mulVec w) (transformedNormal B u w)
        (transformedSecondData B H) =
      curvature u w (normal u w) H / (|B.det| ^ 2 * alpha B u w ^ 4) := by
  unfold curvature
  rw [secondForm_transformed_det B hB, gram_transformed B hB u w hreg]
  ring

theorem secondForm_smul_det (a : ℝ) (n : Space) (H : SecondData) :
    (secondForm (a • n) H).det = a ^ 2 * (secondForm n H).det := by
  simp only [Matrix.det_fin_two, secondForm, dot_smul_left]
  ring

theorem canonical_transformed_normal (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) (hreg : 0 < dotProduct (cross u w) (cross u w)) :
    normal (B.mulVec u) (B.mulVec w) =
      (B.det / |B.det|) • transformedNormal B u w := by
  have ha0 := ne_of_gt (area_pos u w hreg)
  have hp0 := ne_of_gt (alpha_pos B hB u w hreg)
  have hv0 : |B.det| ≠ 0 := abs_ne_zero.mpr hB
  have hn : transport B (cross u w) = area u w • transport B (normal u w) := by
    simp [transport, normal, Matrix.mulVec_smul, smul_smul, ha0]
  rw [normal, area_transformed B hB u w hreg, cross_mulVec B hB]
  change (|B.det| * alpha B u w * area u w)⁻¹ • (B.det • transport B (cross u w)) = _
  rw [hn]
  dsimp only [transformedNormal]
  simp only [smul_smul]
  congr 1
  field_simp
  ring

theorem curvature_canonical_transformed (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (u w : Space) (hreg : 0 < dotProduct (cross u w) (cross u w)) (H : SecondData) :
    curvature (B.mulVec u) (B.mulVec w) (normal (B.mulVec u) (B.mulVec w))
        (transformedSecondData B H) =
      curvature u w (normal u w) H / (|B.det| ^ 2 * alpha B u w ^ 4) := by
  have hsign : (B.det / |B.det|) ^ 2 = 1 := by
    rw [div_pow, sq_abs]
    exact div_self (pow_ne_zero 2 hB)
  rw [canonical_transformed_normal B hB u w hreg]
  have hc : curvature (B.mulVec u) (B.mulVec w)
      ((B.det / |B.det|) • transformedNormal B u w) (transformedSecondData B H) =
      curvature (B.mulVec u) (B.mulVec w) (transformedNormal B u w)
        (transformedSecondData B H) := by
    simp only [curvature, secondForm_smul_det, hsign, one_mul]
  rw [hc]
  exact curvature_transformed B hB u w hreg H

end PaperI.AffineSurfaceAlgebra
