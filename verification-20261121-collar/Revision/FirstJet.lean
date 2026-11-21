import PaperILean.Nov18CollarReciprocal
import PaperILean.SpectralHessianForm

open Set Filter MeasureTheory Matrix
open scoped ContDiff Topology Matrix.L2OpNorm
noncomputable section
namespace PaperI.CollarRevision
open CommonNullAssignment BoundedCharacteristic ParabolicCollar CollarScalar CollarNet

private theorem operator_le_hilbert_schmidt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖A‖ ≤ matrixFullHSNorm A := by
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ _
  apply ContinuousLinearMap.opNorm_le_bound _ (matrixFullHSNorm_nonneg _)
  intro x
  let v : Fin n → ℝ := (WithLp.equiv 2 (Fin n → ℝ)) x
  have hx : (WithLp.equiv 2 (Fin n → ℝ)).symm v = x := (WithLp.equiv 2 _).symm_apply_apply x
  rw [← hx, Matrix.toEuclideanCLM_piLp_equiv_symm, Matrix.toLin'_apply]
  change ‖(WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm (A *ᵥ v)‖ ≤
    matrixFullHSNorm A * ‖(WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm v‖
  rw [← coordinateL2Norm_eq_norm, ← coordinateL2Norm_eq_norm]
  apply (sq_le_sq₀ (coordinateL2Norm_nonneg _) (mul_nonneg (matrixFullHSNorm_nonneg _) (coordinateL2Norm_nonneg _))).mp
  simp only [coordinateL2Norm_sq, mul_pow, matrixFullHSNorm_sq, Matrix.mulVec, dotProduct]
  calc
    _ ≤ ∑ i, (∑ j, (A i j)^2) * (∑ j, (v j)^2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) v)
    _ = _ := by rw [Finset.sum_mul]


/-- The error has only its top row. The determinant is the actual collar Jacobian. -/
theorem centered_first_jet {ι : Type} [DecidableEq ι] {k N e es rate sf df : ℕ}
    {F : CoefficientSpace k} {P Λ δ U B : ℝ} {E : Set Plane} {c d v : Plane → ℝ}
    {keep : Plane → Prop} {labels : Finset ι} {rep : ι → Plane} {fixed : ι → Fin 6 → ℝ}
    {route : CertificateRoute} {tag : ℝ × ℝ}
    (Q : OriginalParabolicBandResult F P Λ δ U B N e es rate sf df E c d v keep labels rep fixed route tag)
    {q : Plane} (hq : q∈Q.certificate.certificate.prepared.goodParam) (hP : 2≤P)
    (hδ : 0≤δ) (hsmall : P^es*δ≤1/4)
    (hγ : ContDiffOn ℝ ∞ Q.γ (Ioo Q.a Q.b)) (hd : ContDiffOn ℝ ∞ (d ∘ Q.γ) (Ioo Q.a Q.b))
    (hv : ContDiffOn ℝ ∞ (v ∘ Q.γ) (Ioo Q.a Q.b)) :
    let S := centeredSeedAt Q.γ d v q
    let ν := deriv S.b 0
    deriv S.a 0 = Q.det ![q.1,q.2]+ν*S.d 0 ∧
      |ν|≤1 ∧ |S.d 0|≤P^es*δ ∧
      ‖(!![deriv S.a 0,S.d 0;ν,1] - !![1,0;ν,1] : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ P^(es+1)*δ := by
  intro S ν
  have hg := Q.centered q hq
  have hA : |deriv S.a 0-1|≤P^es*δ := hg.linear.1
  have hB : |ν|≤1 := hg.linear.2.1
  have hD : |S.d 0|≤P^es*δ := hg.linear.2.2.1
  have hJ := (same_good_reciprocal Q hq hP hsmall hγ hd hv).1.self_of_nhds
  have hj : S.jac 0=Q.det ![q.1,q.2] := by simpa only [add_zero] using hJ
  refine ⟨?_,hB,hD,?_⟩
  · rw [←hj]
    simp [Seed.jac,ν]
    ring
  · let M : Matrix (Fin 2) (Fin 2) ℝ := !![deriv S.a 0,S.d 0;ν,1] - !![1,0;ν,1]
    let t := P^es*δ
    have ht : 0≤t := mul_nonneg (pow_nonneg (by linarith) _) hδ
    have h₂ : matrixFullHSNorm M ≤ 2*t := by
      apply (sq_le_sq₀ (matrixFullHSNorm_nonneg _) (by linarith : 0≤2*t)).mp
      rw [matrixFullHSNorm_sq]
      simp [M,Fin.sum_univ_two]
      have hA₂ := pow_le_pow_left₀ (abs_nonneg _) hA 2
      have hD₂ := pow_le_pow_left₀ (abs_nonneg _) hD 2
      rw [sq_abs] at hA₂ hD₂
      change _ ≤ t^2 at hA₂ hD₂
      nlinarith only [hA₂,hD₂,sq_nonneg t]
    apply ((operator_le_hilbert_schmidt M).trans h₂).trans
    rw [pow_succ]
    change 2*(P^es*δ)≤P^es*P*δ
    exact (mul_le_mul_of_nonneg_right hP ht).trans_eq (by dsimp [t]; ring)

end PaperI.CollarRevision
