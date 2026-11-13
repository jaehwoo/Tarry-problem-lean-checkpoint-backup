import PaperILean.ParabolicCollarGeometry

open Set Filter
noncomputable section

namespace PaperI.ParabolicCollar
open BoundedCharacteristic

def thetaMap (d : ℝ) : Coordinates →L[ℝ] Coordinates := matrixMap !![1,-d;0,1]

def coframeMatrix (J ν C : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![J+ν*C,C;ν,1]

def inverseCoframe (J ν C : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1/J,-C/J;-ν/J,(J+ν*C)/J]

private theorem matrixMap_apply' (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Coordinates) (i : Fin 2) :
    matrixMap A x i = A i 0*x 0+A i 1*x 1 := by
  change (Matrix.toLin' A) x i = _
  rw [Matrix.toLin'_apply]
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem coframe_pullback {A ν D V D' V' t e : ℝ} :
    let L := matrixMap (collarJac A ν D V D' V' t)
    (thetaMap e).comp L = matrixMap (coframeMatrix L.det ν (D+V*t-e)) := by
  dsimp only
  rw [matrixMap_det,Matrix.det_fin_two]
  ext x i
  fin_cases i <;> simp [thetaMap,collarJac,coframeMatrix,matrixMap_apply'] <;> ring

theorem coframe_inverse {J ν C : ℝ} (hJ : J≠0) :
    coframeMatrix J ν C * inverseCoframe J ν C = 1 ∧
      inverseCoframe J ν C * coframeMatrix J ν C = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [coframeMatrix,inverseCoframe,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply] <;>
    field_simp <;> ring

private theorem opNorm_le_of_entry_bound (A : Matrix (Fin 2) (Fin 2) ℝ) {R : ℝ} (hR : 0≤R)
    (hA : ∀ i j, |A i j|≤R) : ‖matrixMap A‖≤2*R := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  rw [matrixMap_apply',Real.norm_eq_abs]
  calc
    |A i 0*x 0+A i 1*x 1| ≤ |A i 0*x 0|+|A i 1*x 1| := abs_add ..
    _ = |A i 0| * |x 0|+|A i 1| * |x 1| := by rw [abs_mul,abs_mul]
    _ ≤ R*‖x‖+R*‖x‖ := by
      apply add_le_add <;> apply mul_le_mul (hA _ _) _ (abs_nonneg _) hR <;>
        simpa [Real.norm_eq_abs] using norm_le_pi_norm x _
    _ = 2*R*‖x‖ := by ring

theorem coframe_norms {J ν C : ℝ} (hJ₀ : 1/2≤J) (hJ₁ : J≤3/2)
    (hν : |ν|≤1) (hC : |C|≤1) :
    ‖matrixMap (coframeMatrix J ν C)‖≤5 ∧ ‖matrixMap (inverseCoframe J ν C)‖≤10 := by
  have hJ : 0<J := by linarith
  have hmain : |J+ν*C|≤5/2 := calc
    |J+ν*C| ≤ |J|+|ν*C| := abs_add ..
    _ ≤ 5/2 := by
      rw [abs_of_pos hJ,abs_mul]
      have hmul : |ν| * |C|≤1 := by nlinarith [mul_le_mul hν hC (abs_nonneg C) (by norm_num : (0:ℝ)≤1)]
      linarith
  have hdiv {x : ℝ} (hx : |x|≤5/2) : |x/J|≤5 := by
    rw [abs_div,abs_of_pos hJ,div_le_iff₀ hJ]
    linarith
  constructor
  · have h := opNorm_le_of_entry_bound (coframeMatrix J ν C) (R:=5/2) (by norm_num) (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [coframeMatrix]
      · exact hmain
      · linarith
      · linarith
      · norm_num)
    norm_num at h ⊢
    exact h
  · have h := opNorm_le_of_entry_bound (inverseCoframe J ν C) (R:=5) (by norm_num) (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp only [inverseCoframe,Matrix.of_apply,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val_succ] <;> apply hdiv
      · norm_num
      · rw [abs_neg]
        linarith
      · rw [abs_neg]
        linarith
      · exact hmain)
    norm_num at h ⊢
    exact h

theorem collar_det_bounds {m h u V' t : ℝ} (hm : 1≤m) (hh : 0≤h)
    (hsmall : h*m^3≤1/16) (hu : |u|≤h) (hV' : |V'|≤2*h) (ht : |t|≤m) :
    1/2≤1+u*t+V'*t^2/2 ∧ 1+u*t+V'*t^2/2≤3/2 := by
  have hm₀ : 0≤m := by linarith
  have hm₁ : m≤m^3 := calc
    m = m*1^2 := by ring
    _ ≤ m*m^2 := by gcongr
    _ = m^3 := by ring
  have hm₂ : m^2≤m^3 := calc
    m^2 = m^2*1 := by ring
    _ ≤ m^2*m := by gcongr
    _ = m^3 := by ring
  have h₁ : |u*t|≤1/16 := by
    rw [abs_mul]
    exact (mul_le_mul hu ht (abs_nonneg _) hh).trans
      ((mul_le_mul_of_nonneg_left hm₁ hh).trans hsmall)
  have h₂ : |V'*t^2/2|≤1/16 := by
    rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg t),abs_of_pos (show (0:ℝ)<2 by norm_num),
      div_le_iff₀ (by norm_num : (0:ℝ)<2)]
    have hsq : t^2≤m^2 := by
      rw [←sq_abs t]
      exact pow_le_pow_left₀ (abs_nonneg _) ht _
    calc
      |V'| * t^2 ≤ (2*h)*m^2 := mul_le_mul hV' hsq (sq_nonneg _) (by positivity)
      _ = 2*(h*m^2) := by ring
      _ ≤ 2*(h*m^3) := by gcongr
      _ ≤ _ := by linarith
  have h₁' := abs_le.mp h₁
  have h₂' := abs_le.mp h₂
  constructor <;> linarith

end PaperI.ParabolicCollar
