import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Set MeasureTheory
open scoped Topology

namespace PaperII.VOutputBand

abbrev GraphPlane := ℝ × ℝ

/-- Ordinary partial differentiation in a fixed Cartesian direction. -/
noncomputable def graphPartial (direction : GraphPlane) (c : GraphPlane → ℝ)
    (x : GraphPlane) : ℝ :=
  fderiv ℝ c x direction

noncomputable def graphY (c : GraphPlane → ℝ) := graphPartial (1, 0) c
noncomputable def graphZ (c : GraphPlane → ℝ) := graphPartial (0, 1) c

/-- The rate is the derivative in the actual null field, not in a
coordinate-dependent reparametrization of that field. -/
noncomputable def nullRate (d : GraphPlane → ℝ) (x : GraphPlane) : ℝ :=
  fderiv ℝ d x (d x, 1)

private theorem graphPartial_contDiffAt {c : GraphPlane → ℝ} {x w : GraphPlane}
    {n : WithTop ℕ∞} (hc : ContDiffAt ℝ (n + 1) c x) :
    ContDiffAt ℝ n (graphPartial w c) x := by
  exact (hc.fderiv_right le_rfl).clm_apply contDiffAt_const

/-- II4332–4340. Differentiate the actual null identity at the normalized endpoint.
The same proof does not need the vanishing of the first graph jet. -/
theorem ordinary_graph_row
    {c d : GraphPlane → ℝ} {x : GraphPlane}
    (hc : ContDiffAt ℝ 3 c x) (hd : DifferentiableAt ℝ d x) (hd₀ : d x = 0)
    (hnull : (fun p =>
      graphZ (graphZ c) p + 2 * d p * graphZ (graphY c) p + d p ^ 2 * graphY (graphY c) p)
        =ᶠ[𝓝 x] 0) :
    graphZ (graphZ (graphZ c)) x + 2 * graphZ (graphY c) x * nullRate d x = 0 := by
  have hc₂ (w : GraphPlane) : ContDiffAt ℝ 2 (graphPartial w c) x := by
    apply graphPartial_contDiffAt
    simpa using hc
  have hc₁ (w w' : GraphPlane) :
      DifferentiableAt ℝ (graphPartial w' (graphPartial w c)) x := by
    apply ContDiffAt.differentiableAt (n := 1) _ le_rfl
    apply graphPartial_contDiffAt
    simpa using hc₂ w
  have hzz := (hc₁ (0, 1) (0, 1)).hasFDerivAt
  have hyz := (hc₁ (1, 0) (0, 1)).hasFDerivAt
  have hyy := (hc₁ (1, 0) (1, 0)).hasFDerivAt
  have h := (hzz.add ((hd.hasFDerivAt.const_mul 2).mul hyz)).add
    ((hd.hasFDerivAt.mul hd.hasFDerivAt).mul hyy)
  have hzero := h.congr_of_eventuallyEq (by simpa only [pow_two] using hnull.symm)
  have hder := congrArg (fun L : GraphPlane →L[ℝ] ℝ => L (0, 1)) hzero.fderiv
  simp [graphY, graphZ, graphPartial, nullRate, hd₀, add_comm, mul_assoc, mul_left_comm,
    mul_comm] at hder ⊢
  exact hder.symm

variable {ι : Type*} [DecidableEq ι]

/-- The change between corresponding output fibers. -/
noncomputable def replaceCubic (mixed cubic : ι) (w : ι → ℝ) : ι → ℝ :=
  Function.update w cubic (-w cubic / (2 * w mixed))

/-- The inverse change, defined on the entire output space. -/
def restoreCubic (mixed cubic : ι) (w : ι → ℝ) : ι → ℝ :=
  Function.update w cubic (-(2 * w mixed) * w cubic)

theorem restore_replaceCubic (mixed cubic : ι) (hrows : mixed ≠ cubic)
    (w : ι → ℝ) (hB : w mixed ≠ 0) :
    restoreCubic mixed cubic (replaceCubic mixed cubic w) = w := by
  ext i
  by_cases hi : i = cubic
  · subst i
    simp [restoreCubic, replaceCubic, hrows]
    field_simp
  · simp [restoreCubic, replaceCubic, hi]

theorem replace_restoreCubic (mixed cubic : ι) (hrows : mixed ≠ cubic)
    (w : ι → ℝ) (hB : w mixed ≠ 0) :
    replaceCubic mixed cubic (restoreCubic mixed cubic w) = w := by
  ext i
  by_cases hi : i = cubic
  · subst i
    simp [restoreCubic, replaceCubic, hrows]
    field_simp
  · simp [restoreCubic, replaceCubic, hi]

variable [Fintype ι]

/-- The Cartesian Jacobian is evaluated on the standard coordinate unit vectors. -/
noncomputable def ordinaryJacobian (F : (ι → ℝ) → (ι → ℝ)) (x : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j => fderiv ℝ F x (Pi.single j 1) i

private theorem ordinaryJacobian_row {F : (ι → ℝ) → (ι → ℝ)} {x : ι → ℝ}
    (hF : DifferentiableAt ℝ F x) (i : ι) :
    ordinaryJacobian F x i = fun j => fderiv ℝ (fun p => F p i) x (Pi.single j 1) := by
  have h := (hasFDerivAt_pi'.1 hF.hasFDerivAt i).fderiv
  ext j
  rw [h]
  rfl

private theorem restoreJacobian {F G : (ι → ℝ) → (ι → ℝ)} {x : ι → ℝ}
    {mixed cubic : ι} (hrows : mixed ≠ cubic)
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x)
    (hchange : F =ᶠ[𝓝 x] fun p => restoreCubic mixed cubic (G p)) :
    (ordinaryJacobian F x).det =
      -(2 * G x mixed) * (ordinaryJacobian G x).det := by
  let J := ordinaryJacobian G x
  have hc := hasFDerivAt_pi'.1 hG.hasFDerivAt cubic
  have hm := hasFDerivAt_pi'.1 hG.hasFDerivAt mixed
  have hmatrix : ordinaryJacobian F x = J.updateRow cubic
      ((-(2 * G x mixed)) • J cubic + (-(2 * G x cubic)) • J mixed) := by
    ext i j
    by_cases hi : i = cubic
    · subst i
      have hp := (hm.const_mul (-2)).mul hc
      have heq : (fun p => F p cubic) =ᶠ[𝓝 x]
          (fun p => -2 * G p mixed * G p cubic) := hchange.mono fun p hp' => by
        simp [hp', restoreCubic]
      rw [ordinaryJacobian_row hF, Matrix.updateRow_self, (hp.congr_of_eventuallyEq heq).fderiv]
      change _ = _ * fderiv ℝ G x (Pi.single j 1) cubic +
        _ * fderiv ℝ G x (Pi.single j 1) mixed
      simp
      ring
    · have heq : (fun p => F p i) =ᶠ[𝓝 x] (fun p => G p i) :=
        hchange.mono fun p hp => by simp [hp, restoreCubic, hi]
      rw [ordinaryJacobian_row hF, Matrix.updateRow_ne hi,
        ((hasFDerivAt_pi'.1 hG.hasFDerivAt i).congr_of_eventuallyEq heq).fderiv]
      rfl
  rw [hmatrix, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.det_updateRow_smul, Matrix.det_updateRow_eq_zero hrows,
    Matrix.updateRow_eq_self, mul_zero, add_zero]

/-- The union includes its endpoints and allows coincident bands at zero. -/
theorem signed_band_eq (a b : ℝ) (ha : 0 ≤ a) :
    {v : ℝ | a ≤ |v| ∧ |v| ≤ b} = Icc (-b) (-a) ∪ Icc a b := by
  ext v
  simp only [mem_setOf_eq, mem_union, mem_Icc, le_abs, abs_le]
  constructor
  · rintro ⟨h | h, hl, hr⟩
    · exact Or.inr ⟨h, hr⟩
    · exact Or.inl ⟨hl, by linarith⟩
  · rintro (⟨hl, hv⟩ | ⟨hv, hr⟩)
    · exact ⟨Or.inr (by linarith), hl, by linarith⟩
    · exact ⟨Or.inl hv, by linarith, hr⟩

/-- Ordinary Lebesgue length bound for the two signed bands. -/
theorem signed_band_volume (c₀ C₀ ν : ℝ) (hc₀ : 0 ≤ c₀) (hC₀ : c₀ ≤ C₀) (hν : 0 ≤ ν) :
    volume {v : ℝ | c₀ * ν ≤ |v| ∧ |v| ≤ C₀ * ν} ≤
      ENNReal.ofReal (2 * (C₀ - c₀) * ν) := by
  rw [signed_band_eq (c₀ * ν) (C₀ * ν) (mul_nonneg hc₀ hν)]
  refine (measure_union_le _ _).trans ?_
  rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add]
  · apply le_of_eq
    congr 1
    ring
  · linarith [mul_le_mul_of_nonneg_right hC₀ hν]
  · exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right hC₀ hν)


private theorem differentiableAt_replaceCubic {F : (ι → ℝ) → (ι → ℝ)} {x : ι → ℝ}
    (mixed cubic : ι) (hF : DifferentiableAt ℝ F x) (hB : F x mixed ≠ 0) :
    DifferentiableAt ℝ (fun p => replaceCubic mixed cubic (F p)) x := by
  apply differentiableAt_pi.2
  intro i
  by_cases hi : i = cubic
  · subst i
    have hc := (differentiableAt_pi.1 hF cubic).neg
    have hden := (differentiableAt_pi.1 hF mixed).const_mul 2
    have hInv := hden.inv (mul_ne_zero two_ne_zero hB)
    simpa [replaceCubic, div_eq_mul_inv] using hc.mul hInv
  · simpa [replaceCubic, hi] using differentiableAt_pi.1 hF i

/-- The new atlas records the actual rate at the same endpoint and changes no other row. -/
noncomputable def actualRateAtlas (cubic : ι) (F : (ι → ℝ) → (ι → ℝ))
    (d : (ι → ℝ) → GraphPlane → ℝ) (x : (ι → ℝ) → GraphPlane) (p : ι → ℝ) :
    ι → ℝ :=
  Function.update (F p) cubic (nullRate (d p) (x p))

omit [Fintype ι] in
private theorem actualRateAtlas_eq {mixed cubic : ι}
    {F : (ι → ℝ) → (ι → ℝ)} {c d : (ι → ℝ) → GraphPlane → ℝ}
    {x : (ι → ℝ) → GraphPlane} {p : ι → ℝ}
    (hc : ContDiffAt ℝ 3 (c p) (x p))
    (hd : DifferentiableAt ℝ (d p) (x p)) (hd₀ : d p (x p) = 0)
    (hnull : (fun q => graphZ (graphZ (c p)) q +
      2 * d p q * graphZ (graphY (c p)) q + d p q ^ 2 * graphY (graphY (c p)) q)
        =ᶠ[𝓝 (x p)] 0)
    (hmixed : F p mixed = graphZ (graphY (c p)) (x p))
    (hcubic : F p cubic = graphZ (graphZ (graphZ (c p))) (x p))
    (hB : F p mixed ≠ 0) :
    actualRateAtlas cubic F d x p = replaceCubic mixed cubic (F p) := by
  have h := ordinary_graph_row hc hd hd₀ hnull
  rw [← hmixed, ← hcubic] at h
  have hrate : nullRate (d p) (x p) = -F p cubic / (2 * F p mixed) := by
    apply (eq_div_iff (mul_ne_zero two_ne_zero hB)).2
    linarith only [h]
  simp [actualRateAtlas, replaceCubic, hrate]

private theorem transformed_atlas_jacobians {mixed cubic : ι}
    {F G : (ι → ℝ) → (ι → ℝ)} {p : ι → ℝ}
    (hrows : mixed ≠ cubic) (hF : DifferentiableAt ℝ F p)
    (hB : F p mixed ≠ 0)
    (heq : G =ᶠ[𝓝 p] fun q => replaceCubic mixed cubic (F q)) :
    DifferentiableAt ℝ G p ∧
      (ordinaryJacobian G p).det = -(2 * F p mixed)⁻¹ * (ordinaryJacobian F p).det ∧
      |(ordinaryJacobian G p).det|⁻¹ = (2 * |F p mixed|) * |(ordinaryJacobian F p).det|⁻¹ := by
  have hG := (differentiableAt_replaceCubic mixed cubic hF hB).congr_of_eventuallyEq heq
  have hlocalB : ∀ᶠ q in 𝓝 p, F q mixed ≠ 0 :=
    (differentiableAt_pi.1 hF mixed).continuousAt.eventually_ne hB
  have hinv : F =ᶠ[𝓝 p] fun q => restoreCubic mixed cubic (G q) := by
    filter_upwards [heq, hlocalB] with q hq hqB
    rw [hq, restore_replaceCubic mixed cubic hrows _ hqB]
  have hdet := restoreJacobian hrows hF hG hinv
  rw [heq.eq_of_nhds, replaceCubic, Function.update_of_ne hrows] at hdet
  refine ⟨hG, ?_, ?_⟩
  · rw [hdet]
    field_simp
  · rw [hdet, abs_mul, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_inv]
    symm
    exact mul_inv_cancel_left₀ (mul_ne_zero two_ne_zero (abs_ne_zero.mpr hB)) _

/-- Paper II, II4342–4348. The equality is of the entire corresponding fibers on
the branch. The determinant and inverse density are computed on the actual atlas.
The index type may be the retained row set after the normalization rows have been removed. -/
theorem band_interval_in_coefficient_map
    {mixed cubic : ι} (hrows : mixed ≠ cubic)
    {F : (ι → ℝ) → (ι → ℝ)} {c d : (ι → ℝ) → GraphPlane → ℝ}
    {x : (ι → ℝ) → GraphPlane} {U : Set (ι → ℝ)} (hU : IsOpen U)
    {bmin bmax : ℝ} (hbmin : 0 < bmin)
    (hF : ∀ p ∈ U, DifferentiableAt ℝ F p)
    (hB : ∀ p ∈ U, bmin ≤ |F p mixed| ∧ |F p mixed| ≤ bmax)
    (hc : ∀ p ∈ U, ContDiffAt ℝ 3 (c p) (x p))
    (hd : ∀ p ∈ U, DifferentiableAt ℝ (d p) (x p))
    (hnorm : ∀ p ∈ U, d p (x p) = 0)
    (hnull : ∀ p ∈ U, (fun q => graphZ (graphZ (c p)) q +
      2 * d p q * graphZ (graphY (c p)) q + d p q ^ 2 * graphY (graphY (c p)) q)
        =ᶠ[𝓝 (x p)] 0)
    (hmixed : ∀ p ∈ U, F p mixed = graphZ (graphY (c p)) (x p))
    (hcubic : ∀ p ∈ U, F p cubic = graphZ (graphZ (graphZ (c p))) (x p))
    {c₀ C₀ ν : ℝ} (hc₀ : 0 ≤ c₀) (hC₀ : c₀ ≤ C₀) (hν : 0 ≤ ν) :
    let G := actualRateAtlas cubic F d x
    (∀ w : ι → ℝ, {p ∈ U | G p = replaceCubic mixed cubic w} = {p ∈ U | F p = w}) ∧
    (∀ N : ℕ, (∀ w : ι → ℝ, {p ∈ U | F p = w}.Finite ∧ {p ∈ U | F p = w}.ncard ≤ N) →
      ∀ w : ι → ℝ, {p ∈ U | G p = w}.Finite ∧ {p ∈ U | G p = w}.ncard ≤ N) ∧
    (∀ p ∈ U, DifferentiableAt ℝ G p ∧
      (ordinaryJacobian G p).det = -(2 * F p mixed)⁻¹ * (ordinaryJacobian F p).det ∧
      |(ordinaryJacobian G p).det|⁻¹ =
        (2 * |F p mixed|) * |(ordinaryJacobian F p).det|⁻¹) ∧
    volume ((fun p => G p cubic) '' {p ∈ U | c₀ * ν ≤ |G p cubic| ∧ |G p cubic| ≤ C₀ * ν}) ≤
      ENNReal.ofReal (2 * (C₀ - c₀) * ν) := by
  dsimp only
  have hnz (p) (hp : p ∈ U) : F p mixed ≠ 0 :=
    abs_pos.mp (hbmin.trans_le (hB p hp).1)
  have heq (p) (hp : p ∈ U) :
      actualRateAtlas cubic F d x p = replaceCubic mixed cubic (F p) :=
    actualRateAtlas_eq (hc p hp) (hd p hp) (hnorm p hp) (hnull p hp)
      (hmixed p hp) (hcubic p hp) (hnz p hp)
  have hfibers (w : ι → ℝ) :
      {p ∈ U | actualRateAtlas cubic F d x p = replaceCubic mixed cubic w} =
        {p ∈ U | F p = w} := by
    ext p
    constructor
    · rintro ⟨hp, hfiber⟩
      have hw : F p mixed = w mixed := by
        simpa [heq p hp, replaceCubic, hrows] using congrFun hfiber mixed
      have hwb : w mixed ≠ 0 := hw ▸ hnz p hp
      have hf := congrArg (restoreCubic mixed cubic) ((heq p hp).symm.trans hfiber)
      simpa [restore_replaceCubic, hrows, hnz p hp, hwb] using And.intro hp hf
    · rintro ⟨hp, hfiber⟩
      exact ⟨hp, (heq p hp).trans (congrArg (replaceCubic mixed cubic) hfiber)⟩
  refine ⟨hfibers, ?_, ?_, ?_⟩
  · intro N hN w
    by_cases hw : w mixed = 0
    · have hempty : {p ∈ U | actualRateAtlas cubic F d x p = w} = ∅ := by
        ext p
        constructor
        · rintro ⟨hp, hpw⟩
          have hz : F p mixed = 0 := by
            simpa [heq p hp, replaceCubic, hrows, hw] using congrFun hpw mixed
          exact (hnz p hp hz).elim
        · simp
      simp [hempty]
    · have h := hfibers (restoreCubic mixed cubic w)
      rw [replace_restoreCubic mixed cubic hrows w hw] at h
      rw [h]
      exact hN _
  · intro p hp
    apply transformed_atlas_jacobians hrows (hF p hp) (hnz p hp)
    filter_upwards [hU.mem_nhds hp] with q hq
    exact heq q hq
  · refine (measure_mono ?_).trans (signed_band_volume c₀ C₀ ν hc₀ hC₀ hν)
    rintro v ⟨p, ⟨_, hp⟩, rfl⟩
    exact hp

end PaperII.VOutputBand

