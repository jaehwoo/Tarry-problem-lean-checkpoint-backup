import PaperILean.LinearNonautonomousODE
import PaperILean.LocalHorizontalFrame

/-! I292: global horizontal lifting on a prescribed interval. The linear
equation Bdot=(1/2) Qdot Q^-1 B is solved before Gram conservation is proved.
No commutativity, uniform eigenvalue bound, or uniform constants are assumed. -/
noncomputable section
open Set Filter
open scoped Matrix Matrix.L2OpNorm Topology ContDiff
namespace PaperI

def horizontalLinearCoefficient {n : ℕ} (Q D : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := (1 / 2 : ℝ) • (D * Q⁻¹)

theorem horizontalLinearCoefficient_gram {n : ℕ}
    (Q D : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm) (hD : D.IsSymm)
    (hu : IsUnit Q) :
    horizontalLinearCoefficient Q D * Q + Q * (horizontalLinearCoefficient Q D)ᵀ = D := by
  have hi := Matrix.nonsing_inv_mul Q ((Matrix.isUnit_iff_isUnit_det Q).mp hu)
  have he : horizontalLinearCoefficient Q D * Q = (1 / 2 : ℝ) • D := by
    simp only [horizontalLinearCoefficient, Matrix.smul_mul, Matrix.mul_assoc, hi, Matrix.mul_one]
  have ht : Q * (horizontalLinearCoefficient Q D)ᵀ = (1 / 2 : ℝ) • D := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, hQ.eq, hD.eq] using
      congrArg Matrix.transpose he
  rw [he, ht, ← add_smul]
  norm_num

theorem horizontalLinearCoefficient_mul {n : ℕ}
    (D B : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit B) :
    horizontalLinearCoefficient (B * Bᵀ) D * B = horizontalFrameVelocity D B := by
  have hi := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hu)
  simp only [horizontalLinearCoefficient, horizontalFrameVelocity, Matrix.mul_inv_rev,
    ← Matrix.transpose_nonsing_inv, Matrix.smul_mul, Matrix.mul_assoc, hi, Matrix.mul_one]

def gramLinearOperator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ContinuousLinearMap.mul ℝ _ A + (ContinuousLinearMap.mul ℝ _).flip Aᵀ

theorem gramLinearOperator_apply {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℝ) :
    gramLinearOperator A C = A * C + C * Aᵀ := rfl

theorem contDiff_gramLinearOperator {n : ℕ} :
    ContDiff ℝ ⊤ (gramLinearOperator (n := n)) := by
  exact (ContinuousLinearMap.mul ℝ _).contDiff.add
    ((ContinuousLinearMap.mul ℝ _).flip.contDiff.comp
      (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toContinuousLinearEquiv.contDiff)

theorem contDiffOn_horizontalLinearCoefficient (Q : ℝ → SymmetricMatrix 3)
    {s : Set ℝ} (hs : IsOpen s) (hQ : ContDiffOn ℝ ∞ Q s)
    (hp : ∀ t ∈ s, (Q t).val.PosDef) :
    ContDiffOn ℝ ∞ (fun t => horizontalLinearCoefficient (Q t).val (deriv Q t).val) s := by
  have hdQ := ((contDiffOn_infty_iff_deriv_of_isOpen hs).mp hQ).2
  intro t ht
  have hq : ContDiffAt ℝ ∞ (fun u => (Q u).val) t :=
    ((symmetricMatrixIncl 3).contDiff.contDiffAt.of_le (m := ∞) le_top).comp t
      (hQ.contDiffAt (hs.mem_nhds ht))
  have hd : ContDiffAt ℝ ∞ (fun u => (deriv Q u).val) t :=
    ((symmetricMatrixIncl 3).contDiff.contDiffAt.of_le (m := ∞) le_top).comp t
      (hdQ.contDiffAt (hs.mem_nhds ht))
  exact (contDiffAt_const.smul (hd.mul
    (((contDiffAt_matrix_inv (Q t).val (hp t ht).isUnit).of_le (m := ∞) le_top).comp t hq))).contDiffWithinAt

theorem exists_horizontalFrame_Ioo (Q : ℝ → SymmetricMatrix 3)
    {s : Set ℝ} (hs : IsOpen s) (hQ : ContDiffOn ℝ ∞ Q s)
    (hp : ∀ t ∈ s, (Q t).val.PosDef) {a b t₀ : ℝ}
    (his : Icc a b ⊆ s) (ht₀ : t₀ ∈ Ioo a b)
    (B₀ : PositiveFrame) (hGram : B₀.val * B₀.valᵀ = (Q t₀).val) :
    ∃ B : ℝ → Matrix (Fin 3) (Fin 3) ℝ,
      B t₀ = B₀.val ∧ ContDiffOn ℝ ∞ B (Ioo a b) ∧
      ∀ t ∈ Ioo a b, 0 < (B t).det ∧ B t * (B t)ᵀ = (Q t).val ∧
        (horizontalFrameGenerator (deriv Q t).val (B t)).IsSymm ∧
        HasDerivAt B (B t * horizontalFrameGenerator (deriv Q t).val (B t)) t := by
  let A : ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun t => horizontalLinearCoefficient (Q t).val (deriv Q t).val
  have hA : ContDiffOn ℝ ∞ A s := contDiffOn_horizontalLinearCoefficient Q hs hQ hp
  let L : ℝ → (Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ) :=
    fun t => ContinuousLinearMap.mul ℝ _ (A t)
  have hL : ContinuousOn L (Icc a b) :=
    (ContinuousLinearMap.mul ℝ _).continuous.comp_continuousOn (hA.mono his).continuousOn
  obtain ⟨B, hB₀, hB⟩ := exists_linearODE_Ioo L hL ht₀ B₀.val
  have hode : ∀ t ∈ Ioo a b, HasDerivAt B (A t * B t) t := hB
  have hq : ∀ t ∈ Ioo a b,
      HasDerivAt (fun u => (Q u).val) (deriv Q t).val t := by
    intro t ht
    exact (symmetricMatrixIncl 3).hasFDerivAt.comp_hasDerivAt t
      ((hQ.contDiffAt (hs.mem_nhds (his ⟨ht.1.le, ht.2.le⟩))).differentiableAt
        (WithTop.coe_le_coe.mpr le_top)).hasDerivAt
  have hG : ContinuousOn (fun t => gramLinearOperator (A t)) (Icc a b) :=
    contDiff_gramLinearOperator.continuous.comp_continuousOn (hA.mono his).continuousOn
  have hGramB : ∀ t ∈ Ioo a b,
      HasDerivAt (fun u => B u * (B u)ᵀ) (gramLinearOperator (A t) (B t * (B t)ᵀ)) t := by
    intro t ht
    simpa only [gramLinearOperator_apply, Matrix.transpose_mul, Matrix.mul_assoc] using
      hasDerivAt_frameGram (hode t ht)
  have hGramQ : ∀ t ∈ Ioo a b,
      HasDerivAt (fun u => (Q u).val) (gramLinearOperator (A t) (Q t).val) t := by
    intro t ht
    simpa only [gramLinearOperator_apply, A, horizontalLinearCoefficient_gram
      (Q t).val (deriv Q t).val (Q t).property (deriv Q t).property
        (hp t (his ⟨ht.1.le, ht.2.le⟩)).isUnit] using hq t ht
  have heq : EqOn (fun t => B t * (B t)ᵀ) (fun t => (Q t).val) (Ioo a b) := by
    apply linearODE_unique_Ioo (fun t => gramLinearOperator (A t)) hG ht₀ hGramB hGramQ
    simpa only [hB₀] using hGram
  have hdet : ∀ t ∈ Ioo a b, (B t).det ≠ 0 := by
    intro t ht hz
    have hd := congrArg Matrix.det (heq ht)
    rw [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul] at hd
    exact (hp t (his ⟨ht.1.le, ht.2.le⟩)).det_pos.ne' hd.symm
  have hpos : ∀ t ∈ Ioo a b, 0 < (B t).det := by
    intro t ht
    by_contra hn
    have hc : ContinuousOn (fun u => (B u).det) (Ioo a b) :=
      contDiff_matrix_det_three.continuous.comp_continuousOn
        (HasDerivAt.continuousOn hode)
    have hp₀ : 0 < (B t₀).det := by rw [hB₀]; exact B₀.property
    obtain ⟨u, hu, he⟩ := isPreconnected_Ioo.intermediate_value ht ht₀ hc
      (show (0 : ℝ) ∈ Icc (B t).det (B t₀).det from ⟨le_of_not_gt hn, hp₀.le⟩)
    exact hdet u hu he
  have hu : ∀ t ∈ Ioo a b, IsUnit (B t) := fun t ht =>
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hdet t ht))
  have hh : ∀ t ∈ Ioo a b,
      HasDerivAt B (horizontalFrameVelocity (deriv Q t).val (B t)) t := by
    intro t ht
    have ha : A t * B t = horizontalFrameVelocity (deriv Q t).val (B t) := by
      dsimp only [A]
      have heqt : B t * (B t)ᵀ = (Q t).val := heq ht
      rw [← heqt]
      exact horizontalLinearCoefficient_mul _ _ (hu t ht)
    simpa only [ha] using hode t ht
  have hdQ := ((contDiffOn_infty_iff_deriv_of_isOpen hs).mp hQ).2
  have hsm : ContDiffOn ℝ ∞ B (Ioo a b) :=
    contDiffOn_of_smooth_vectorField isOpen_Ioo hh (fun t ht =>
      contDiffAt_horizontalFrameField Q t (B t)
        (hdQ.contDiffAt (hs.mem_nhds (his ⟨ht.1.le, ht.2.le⟩))) (hu t ht))
  refine ⟨B, hB₀, hsm, ?_⟩
  intro t ht
  exact ⟨hpos t ht, heq ht, horizontalFrameGenerator_isSymm _ _ (deriv Q t).property,
    by simpa only [mul_horizontalFrameGenerator _ _ (hu t ht)] using hh t ht⟩


theorem horizontalFrame_unique_Ioo (Q : ℝ → SymmetricMatrix 3)
    {s : Set ℝ} (hs : IsOpen s) (hQ : ContDiffOn ℝ ∞ Q s)
    (hp : ∀ t ∈ s, (Q t).val.PosDef) {a b t₀ : ℝ}
    (his : Icc a b ⊆ s) (ht₀ : t₀ ∈ Ioo a b)
    {B C : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hB : ∀ t ∈ Ioo a b, IsUnit (B t) ∧ B t * (B t)ᵀ = (Q t).val ∧
      HasDerivAt B (horizontalFrameVelocity (deriv Q t).val (B t)) t)
    (hC : ∀ t ∈ Ioo a b, IsUnit (C t) ∧ C t * (C t)ᵀ = (Q t).val ∧
      HasDerivAt C (horizontalFrameVelocity (deriv Q t).val (C t)) t)
    (h₀ : B t₀ = C t₀) : EqOn B C (Ioo a b) := by
  let A : ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun t => horizontalLinearCoefficient (Q t).val (deriv Q t).val
  let L : ℝ → (Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ) :=
    fun t => ContinuousLinearMap.mul ℝ _ (A t)
  have hL : ContinuousOn L (Icc a b) :=
    (ContinuousLinearMap.mul ℝ _).continuous.comp_continuousOn
      ((contDiffOn_horizontalLinearCoefficient Q hs hQ hp).mono his).continuousOn
  have convertPath : ∀ (f : ℝ → Matrix (Fin 3) (Fin 3) ℝ),
      (∀ t ∈ Ioo a b, IsUnit (f t) ∧ f t * (f t)ᵀ = (Q t).val ∧
        HasDerivAt f (horizontalFrameVelocity (deriv Q t).val (f t)) t) →
      ∀ t ∈ Ioo a b, HasDerivAt f (L t (f t)) t := by
    intro f hf t ht
    obtain ⟨hu, hg, hd⟩ := hf t ht
    change HasDerivAt f (horizontalLinearCoefficient (Q t).val (deriv Q t).val * f t) t
    rw [← hg, horizontalLinearCoefficient_mul _ _ hu]
    exact hd
  exact linearODE_unique_Ioo L hL ht₀ (convertPath B hB) (convertPath C hC) h₀

end PaperI

