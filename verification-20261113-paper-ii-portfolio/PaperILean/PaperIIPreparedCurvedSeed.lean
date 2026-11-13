import PaperILean.PaperIIVOutputBand
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open Filter Set
open scoped Topology ContDiff

namespace PaperII.PreparedCurvedSeed

open VOutputBand

noncomputable abbrev S (g : GraphPlane → ℝ) := graphY g
noncomputable abbrev T (g : GraphPlane → ℝ) := graphZ g

/-- The actual pullback is in the order `(s,t)`, with old coordinates `(y,z)`. -/
def seedPoint (ζ : ℝ → ℝ) (p : GraphPlane) : GraphPlane :=
  (p.2 + ζ p.1, p.1)

def seedPullback (ζ : ℝ → ℝ) (c : GraphPlane → ℝ) (p : GraphPlane) : ℝ :=
  c (seedPoint ζ p)

noncomputable def seedSlope (ζ : ℝ → ℝ) (p : GraphPlane) : ℝ :=
  deriv ζ p.1

noncomputable def seedCurvature (ζ : ℝ → ℝ) (p : GraphPlane) : ℝ :=
  deriv (deriv ζ) p.1

private theorem partial_smooth {c : GraphPlane → ℝ} {x u : GraphPlane} {n : WithTop ℕ∞}
    (hc : ContDiffAt ℝ (n + 1) c x) : ContDiffAt ℝ n (graphPartial u c) x :=
  (hc.fderiv_right le_rfl).clm_apply contDiffAt_const

private theorem seedPoint_smooth {ζ : ℝ → ℝ} {p : GraphPlane} {n : WithTop ℕ∞}
    (hζ : ContDiffAt ℝ n ζ p.1) : ContDiffAt ℝ n (seedPoint ζ) p :=
  (contDiffAt_snd.add (hζ.comp p contDiffAt_fst)).prodMk contDiffAt_fst

private theorem pull_smooth {ζ : ℝ → ℝ} {c : GraphPlane → ℝ} {p : GraphPlane}
    {n : WithTop ℕ∞} (hζ : ContDiffAt ℝ n ζ p.1)
    (hc : ContDiffAt ℝ n c (seedPoint ζ p)) : ContDiffAt ℝ n (seedPullback ζ c) p :=
  hc.comp p (seedPoint_smooth hζ)

private theorem pull_deriv {ζ : ℝ → ℝ} {c : GraphPlane → ℝ} {p u : GraphPlane}
    (hζ : DifferentiableAt ℝ ζ p.1) (hc : DifferentiableAt ℝ c (seedPoint ζ p)) :
    graphPartial u (seedPullback ζ c) p =
      (u.2 + seedSlope ζ p * u.1) * graphY c (seedPoint ζ p) +
        u.1 * graphZ c (seedPoint ζ p) := by
  have hz := hζ.hasDerivAt.hasFDerivAt.comp p
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hp := ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.add hz).prodMk
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have h := (hc.hasFDerivAt.comp p hp).fderiv
  have hsplit : (u.2 + seedSlope ζ p * u.1, u.1) =
      (u.2 + seedSlope ζ p * u.1) • ((1, 0) : GraphPlane) + u.1 • ((0, 1) : GraphPlane) := by
    ext <;> simp
  change fderiv ℝ (c ∘ seedPoint ζ) p u = _
  rw [h]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, seedSlope]
  change fderiv ℝ c (seedPoint ζ p) (u.2 + u.1 * deriv ζ p.1, u.1) = _
  rw [mul_comm u.1 (deriv ζ p.1)]
  change fderiv ℝ c (seedPoint ζ p) (u.2 + seedSlope ζ p * u.1, u.1) = _
  rw [hsplit, map_add, map_smul, map_smul]
  rfl

private theorem pull_S {ζ : ℝ → ℝ} {c : GraphPlane → ℝ} {p : GraphPlane}
    (hζ : DifferentiableAt ℝ ζ p.1) (hc : DifferentiableAt ℝ c (seedPoint ζ p)) :
    S (seedPullback ζ c) p =
      seedSlope ζ p * seedPullback ζ (graphY c) p + seedPullback ζ (graphZ c) p := by
  simpa [S, graphY, seedPullback] using pull_deriv (u := (1, 0)) hζ hc

private theorem pull_T {ζ : ℝ → ℝ} {c : GraphPlane → ℝ} {p : GraphPlane}
    (hζ : DifferentiableAt ℝ ζ p.1) (hc : DifferentiableAt ℝ c (seedPoint ζ p)) :
    T (seedPullback ζ c) p = seedPullback ζ (graphY c) p := by
  simpa [T, graphZ, seedPullback] using pull_deriv (u := (0, 1)) hζ hc

private theorem partial_congr {f g : GraphPlane → ℝ} {p u : GraphPlane} (h : f =ᶠ[𝓝 p] g) :
    graphPartial u f p = graphPartial u g p := by
  simp only [graphPartial, h.fderiv_eq]

private theorem near_pull_S {ζ : ℝ → ℝ} {c : GraphPlane → ℝ} {p : GraphPlane}
    (hζ : ContDiffAt ℝ 1 ζ p.1) (hc : ContDiffAt ℝ 1 c (seedPoint ζ p)) :
    S (seedPullback ζ c) =ᶠ[𝓝 p]
      fun q => seedSlope ζ q * seedPullback ζ (graphY c) q + seedPullback ζ (graphZ c) q := by
  filter_upwards
    [((continuous_fst : Continuous (Prod.fst : GraphPlane → ℝ)).continuousAt.tendsto.eventually
      (hζ.eventually (by simp))),
     ((seedPoint_smooth hζ).continuousAt.tendsto.eventually (hc.eventually (by simp)))]
    with q hqζ hqc
  exact pull_S (hqζ.differentiableAt le_rfl) (hqc.differentiableAt le_rfl)

private theorem near_pull_T {ζ : ℝ → ℝ} {c : GraphPlane → ℝ} {p : GraphPlane}
    (hζ : ContDiffAt ℝ 1 ζ p.1) (hc : ContDiffAt ℝ 1 c (seedPoint ζ p)) :
    T (seedPullback ζ c) =ᶠ[𝓝 p] seedPullback ζ (graphY c) := by
  filter_upwards
    [((continuous_fst : Continuous (Prod.fst : GraphPlane → ℝ)).continuousAt.tendsto.eventually
      (hζ.eventually (by simp))),
     ((seedPoint_smooth hζ).continuousAt.tendsto.eventually (hc.eventually (by simp)))]
    with q hqζ hqc
  exact pull_T (hqζ.differentiableAt le_rfl) (hqc.differentiableAt le_rfl)

private theorem partial_add {f g : GraphPlane → ℝ} {p u : GraphPlane}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    graphPartial u (fun q => f q + g q) p = graphPartial u f p + graphPartial u g p := by
  exact congrArg (fun L : GraphPlane →L[ℝ] ℝ => L u)
    (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

private theorem partial_mul {f g : GraphPlane → ℝ} {p u : GraphPlane}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    graphPartial u (fun q => f q * g q) p =
      graphPartial u f p * g p + f p * graphPartial u g p := by
  have h := congrArg (fun L : GraphPlane →L[ℝ] ℝ => L u)
    (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv
  simpa [graphPartial, add_comm, mul_comm] using h

private theorem seedSlope_smooth {ζ : ℝ → ℝ} {p : GraphPlane} {n : WithTop ℕ∞}
    (hζ : ContDiffAt ℝ (n + 1) ζ p.1) : ContDiffAt ℝ n (seedSlope ζ) p := by
  apply ContDiffAt.comp p _ contDiffAt_fst
  exact (hζ.fderiv_right le_rfl).clm_apply contDiffAt_const

private theorem seedCurvature_diff {ζ : ℝ → ℝ} {p : GraphPlane}
    (hζ : ContDiffAt ℝ 3 ζ p.1) : DifferentiableAt ℝ (seedCurvature ζ) p := by
  have h₂ : ContDiffAt ℝ 2 (deriv ζ) p.1 :=
    (hζ.fderiv_right (by decide)).clm_apply contDiffAt_const
  exact (seedSlope_smooth (n := 1) (ζ := deriv ζ) (p := p) (by simpa using h₂)).differentiableAt le_rfl

private theorem slope_S {ζ : ℝ → ℝ} {p : GraphPlane}
    (hζ : ContDiffAt ℝ 2 ζ p.1) : S (seedSlope ζ) p = seedCurvature ζ p := by
  have h₁ : ContDiffAt ℝ 1 (deriv ζ) p.1 :=
    (hζ.fderiv_right (by decide)).clm_apply contDiffAt_const
  have h := ((h₁.differentiableAt le_rfl).hasDerivAt.hasFDerivAt.comp p
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).fderiv
  change fderiv ℝ (deriv ζ ∘ Prod.fst) p (1, 0) = deriv (deriv ζ) p.1
  rw [h]
  simp

private theorem mixed_comm {c : GraphPlane → ℝ} {x u w : GraphPlane}
    (hc : ContDiffAt ℝ 2 c x) :
    graphPartial u (graphPartial w c) x = graphPartial w (graphPartial u c) x := by
  have h := hc.isSymmSndFDerivAt (by simp [minSmoothness]) u w
  have hd : DifferentiableAt ℝ (fderiv ℝ c) x :=
    (hc.fderiv_right (m := 1) (by decide)).differentiableAt le_rfl
  have he (v w' : GraphPlane) :
      graphPartial v (graphPartial w' c) x = fderiv ℝ (fderiv ℝ c) x v w' := by
    have hp := ((ContinuousLinearMap.apply ℝ ℝ w').hasFDerivAt.comp x hd.hasFDerivAt).fderiv
    exact congrArg (fun L : GraphPlane →L[ℝ] ℝ => L v) hp
  simpa only [he] using h

private theorem pull_SS {ζ : ℝ → ℝ} {c : GraphPlane → ℝ} {p : GraphPlane}
    (hζ : ContDiffAt ℝ 2 ζ p.1) (hc : ContDiffAt ℝ 2 c (seedPoint ζ p)) :
    S (S (seedPullback ζ c)) p =
      seedCurvature ζ p * seedPullback ζ (graphY c) p +
      seedSlope ζ p * (seedSlope ζ p * seedPullback ζ (graphY (graphY c)) p +
        seedPullback ζ (graphZ (graphY c)) p) +
      (seedSlope ζ p * seedPullback ζ (graphY (graphZ c)) p +
        seedPullback ζ (graphZ (graphZ c)) p) := by
  have hζ₁ := hζ.of_le (show (1 : WithTop ℕ∞) ≤ 2 by decide)
  have hζd := hζ₁.differentiableAt le_rfl
  have hc₁ := hc.of_le (show (1 : WithTop ℕ∞) ≤ 2 by decide)
  have hY : ContDiffAt ℝ 1 (graphY c) (seedPoint ζ p) := partial_smooth (by simpa using hc)
  have hZ : ContDiffAt ℝ 1 (graphZ c) (seedPoint ζ p) := partial_smooth (by simpa using hc)
  have hβ := (seedSlope_smooth (n := 1) (p := p) (by simpa using hζ)).differentiableAt le_rfl
  have hCY := (pull_smooth hζ₁ hY).differentiableAt le_rfl
  have hCZ := (pull_smooth hζ₁ hZ).differentiableAt le_rfl
  change graphPartial (1, 0) (S (seedPullback ζ c)) p = _
  rw [partial_congr (u := (1, 0)) (near_pull_S hζ₁ hc₁),
    partial_add (hβ.mul hCY) hCZ, partial_mul hβ hCY]
  change S (seedSlope ζ) p * _ + seedSlope ζ p * S (seedPullback ζ (graphY c)) p +
    S (seedPullback ζ (graphZ c)) p = _
  rw [slope_S hζ, pull_S hζd (hY.differentiableAt le_rfl),
    pull_S hζd (hZ.differentiableAt le_rfl)]


private theorem slope_T {ζ : ℝ → ℝ} {p : GraphPlane}
    (hζ : ContDiffAt ℝ 2 ζ p.1) : T (seedSlope ζ) p = 0 := by
  have h₁ : ContDiffAt ℝ 1 (deriv ζ) p.1 :=
    (hζ.fderiv_right (by decide)).clm_apply contDiffAt_const
  have h := ((h₁.differentiableAt le_rfl).hasDerivAt.hasFDerivAt.comp p
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).fderiv
  change fderiv ℝ (deriv ζ ∘ Prod.fst) p (0, 1) = 0
  rw [h]
  simp

private theorem near_pull_SS {ζ : ℝ → ℝ} {c : GraphPlane → ℝ} {p : GraphPlane}
    (hζ : ContDiffAt ℝ 2 ζ p.1) (hc : ContDiffAt ℝ 2 c (seedPoint ζ p)) :
    S (S (seedPullback ζ c)) =ᶠ[𝓝 p] fun q =>
      seedCurvature ζ q * seedPullback ζ (graphY c) q +
      seedSlope ζ q * (seedSlope ζ q * seedPullback ζ (graphY (graphY c)) q +
        seedPullback ζ (graphZ (graphY c)) q) +
      (seedSlope ζ q * seedPullback ζ (graphY (graphZ c)) q +
        seedPullback ζ (graphZ (graphZ c)) q) := by
  filter_upwards
    [((continuous_fst : Continuous (Prod.fst : GraphPlane → ℝ)).continuousAt.tendsto.eventually
      (hζ.eventually (by simp))),
     ((seedPoint_smooth hζ).continuousAt.tendsto.eventually (hc.eventually (by simp)))]
    with q hqζ hqc
  exact pull_SS hqζ hqc

private theorem seed_mixed {ζ : ℝ → ℝ} {c : GraphPlane → ℝ} {p : GraphPlane}
    (hζ : ContDiffAt ℝ 2 ζ p.1) (hc : ContDiffAt ℝ 2 c (seedPoint ζ p)) :
    S (T (seedPullback ζ c)) p =
      seedSlope ζ p * seedPullback ζ (graphY (graphY c)) p +
        seedPullback ζ (graphZ (graphY c)) p ∧
    T (T (seedPullback ζ c)) p = seedPullback ζ (graphY (graphY c)) p := by
  have hζ₁ := hζ.of_le (show (1 : WithTop ℕ∞) ≤ 2 by decide)
  have hc₁ := hc.of_le (show (1 : WithTop ℕ∞) ≤ 2 by decide)
  have hY : ContDiffAt ℝ 1 (graphY c) (seedPoint ζ p) := partial_smooth (by simpa using hc)
  have hq := near_pull_T hζ₁ hc₁
  constructor
  · change graphPartial (1, 0) (T (seedPullback ζ c)) p = _
    rw [partial_congr hq]
    exact pull_S (hζ₁.differentiableAt le_rfl) (hY.differentiableAt le_rfl)
  · change graphPartial (0, 1) (T (seedPullback ζ c)) p = _
    rw [partial_congr hq]
    exact pull_T (hζ₁.differentiableAt le_rfl) (hY.differentiableAt le_rfl)


/-- The two necessary fixed-direction derivatives of the actual second seed row. -/
private theorem third_rows {ζ : ℝ → ℝ} {c : GraphPlane → ℝ} {p : GraphPlane}
    (hζ : ContDiffAt ℝ 3 ζ p.1) (hc : ContDiffAt ℝ 3 c (seedPoint ζ p)) :
    let β := seedSlope ζ p
    let a := seedCurvature ζ p
    let C := seedPullback ζ c
    S (S (S C)) p =
      S (seedCurvature ζ) p * seedPullback ζ (graphY c) p +
        3 * a * (β * seedPullback ζ (graphY (graphY c)) p +
          seedPullback ζ (graphZ (graphY c)) p) +
        β ^ 3 * seedPullback ζ (graphY (graphY (graphY c))) p +
        3 * β ^ 2 * seedPullback ζ (graphZ (graphY (graphY c))) p +
        3 * β * seedPullback ζ (graphZ (graphZ (graphY c))) p +
        seedPullback ζ (graphZ (graphZ (graphZ c))) p ∧
    T (S (S C)) p =
      a * seedPullback ζ (graphY (graphY c)) p +
      β ^ 2 * seedPullback ζ (graphY (graphY (graphY c))) p +
      2 * β * seedPullback ζ (graphZ (graphY (graphY c))) p +
      seedPullback ζ (graphZ (graphZ (graphY c))) p := by
  dsimp only
  have hζ₂ := hζ.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  have hζ₁ := hζ.of_le (show (1 : WithTop ℕ∞) ≤ 3 by decide)
  have hζd := hζ₁.differentiableAt le_rfl
  have hc₂ := hc.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  have hcY (w : GraphPlane) : ContDiffAt ℝ 2 (graphPartial w c) (seedPoint ζ p) :=
    partial_smooth (by simpa using hc)
  have hcYY (w u : GraphPlane) :
      ContDiffAt ℝ 1 (graphPartial u (graphPartial w c)) (seedPoint ζ p) :=
    partial_smooth (by simpa using hcY w)
  have hcY₁ (w : GraphPlane) : ContDiffAt ℝ 1 (graphPartial w c) (seedPoint ζ p) :=
    (hcY w).of_le (by decide)
  have hCY (w : GraphPlane) :
      DifferentiableAt ℝ (seedPullback ζ (graphPartial w c)) p :=
    (pull_smooth hζ₁ (hcY₁ w)).differentiableAt le_rfl
  have hCYY (w u : GraphPlane) :
      DifferentiableAt ℝ (seedPullback ζ (graphPartial u (graphPartial w c))) p :=
    (pull_smooth hζ₁ (hcYY w u)).differentiableAt le_rfl
  have hβ := (seedSlope_smooth (n := 1) (p := p) (by simpa using hζ₂)).differentiableAt le_rfl
  have ha := seedCurvature_diff hζ
  let β := seedSlope ζ
  let a := seedCurvature ζ
  let cy := seedPullback ζ (graphY c)
  let cyy := seedPullback ζ (graphY (graphY c))
  let cyz := seedPullback ζ (graphZ (graphY c))
  let czy := seedPullback ζ (graphY (graphZ c))
  let czz := seedPullback ζ (graphZ (graphZ c))
  have hcy : DifferentiableAt ℝ cy p := hCY (1, 0)
  have hcyy : DifferentiableAt ℝ cyy p := hCYY (1, 0) (1, 0)
  have hcyz : DifferentiableAt ℝ cyz p := hCYY (1, 0) (0, 1)
  have hczy : DifferentiableAt ℝ czy p := hCYY (0, 1) (1, 0)
  have hczz : DifferentiableAt ℝ czz p := hCYY (0, 1) (0, 1)
  have hnear : S (S (seedPullback ζ c)) =ᶠ[𝓝 p]
      a * cy + β * (β * cyy + cyz) + (β * czy + czz) := near_pull_SS hζ₂ hc₂
  have hder (u : GraphPlane) :
      graphPartial u (S (S (seedPullback ζ c))) p =
        graphPartial u a p * cy p + a p * graphPartial u cy p +
        (graphPartial u β p * (β * cyy + cyz) p +
          β p * (graphPartial u β p * cyy p + β p * graphPartial u cyy p +
            graphPartial u cyz p)) +
        (graphPartial u β p * czy p + β p * graphPartial u czy p + graphPartial u czz p) := by
    have h := ((ha.hasFDerivAt.mul hcy.hasFDerivAt).add
      (hβ.hasFDerivAt.mul ((hβ.hasFDerivAt.mul hcyy.hasFDerivAt).add hcyz.hasFDerivAt))).add
      ((hβ.hasFDerivAt.mul hczy.hasFDerivAt).add hczz.hasFDerivAt)
    have h' := h.congr_of_eventuallyEq hnear
    have he := congrArg (fun L : GraphPlane →L[ℝ] ℝ => L u) h'.fderiv
    simp only [graphPartial] at *
    rw [he]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.add_apply, Pi.mul_apply, a, β]
    ring
  have hba : graphPartial (0, 1) a p = 0 := by
    have h₁ : ContDiffAt ℝ 1 (deriv (deriv ζ)) p.1 :=
      ((hζ.fderiv_right (m := 2) (by decide)).clm_apply contDiffAt_const).fderiv_right
        (m := 1) (by decide) |>.clm_apply contDiffAt_const
    have h := ((h₁.differentiableAt le_rfl).hasDerivAt.hasFDerivAt.comp p
        (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).fderiv
    change fderiv ℝ (deriv (deriv ζ) ∘ Prod.fst) p (0, 1) = 0
    rw [h]
    simp
  have hyz : czy p = cyz p := mixed_comm hc₂
  have hyzy :
      seedPullback ζ (graphY (graphZ (graphY c))) p =
        seedPullback ζ (graphZ (graphY (graphY c))) p := mixed_comm (hcY (1, 0))
  have hyzz :
      seedPullback ζ (graphY (graphZ (graphZ c))) p =
        seedPullback ζ (graphZ (graphY (graphZ c))) p := mixed_comm (hcY (0, 1))
  have hfirst_swap (u : GraphPlane) :
      seedPullback ζ (graphPartial u (graphY (graphZ c))) p =
        seedPullback ζ (graphPartial u (graphZ (graphY c))) p := by
    apply partial_congr
    filter_upwards [hc₂.eventually (by simp)] with q hq
    exact mixed_comm hq
  constructor
  · change graphPartial (1, 0) (S (S (seedPullback ζ c))) p = _
    rw [hder]
    change S a p * cy p + a p * S cy p +
      (S β p * (β * cyy + cyz) p +
        β p * (S β p * cyy p + β p * S cyy p + S cyz p)) +
      (S β p * czy p + β p * S czy p + S czz p) = _
    dsimp only [cy, cyy, cyz, czy, czz, β, a]
    rw [slope_S hζ₂,
      pull_S (c := graphY c) hζd ((hcY₁ (1, 0)).differentiableAt le_rfl),
      pull_S (c := graphY (graphY c)) hζd ((hcYY (1, 0) (1, 0)).differentiableAt le_rfl),
      pull_S (c := graphZ (graphY c)) hζd ((hcYY (1, 0) (0, 1)).differentiableAt le_rfl),
      pull_S (c := graphY (graphZ c)) hζd ((hcYY (0, 1) (1, 0)).differentiableAt le_rfl),
      pull_S (c := graphZ (graphZ c)) hζd ((hcYY (0, 1) (0, 1)).differentiableAt le_rfl)]
    rw [show seedPullback ζ (graphY (graphZ c)) p = seedPullback ζ (graphZ (graphY c)) p from hyz,
      hyzz,
      show seedPullback ζ (graphZ (graphY (graphZ c))) p = _ from hfirst_swap (0, 1),
      show seedPullback ζ (graphY (graphY (graphZ c))) p = _ from hfirst_swap (1, 0),
      hyzy, Pi.add_apply, Pi.mul_apply]
    simp only [graphY, graphZ] at hyzy ⊢
    rw [hyzy]
    ring
  · change graphPartial (0, 1) (S (S (seedPullback ζ c))) p = _
    rw [hder, hba]
    change 0 * cy p + a p * T cy p +
      (T β p * (β * cyy + cyz) p +
        β p * (T β p * cyy p + β p * T cyy p + T cyz p)) +
      (T β p * czy p + β p * T czy p + T czz p) = _
    dsimp only [cy, cyy, cyz, czy, czz, β, a]
    rw [slope_T hζ₂,
      pull_T (c := graphY c) hζd ((hcY₁ (1, 0)).differentiableAt le_rfl),
      pull_T (c := graphY (graphY c)) hζd ((hcYY (1, 0) (1, 0)).differentiableAt le_rfl),
      pull_T (c := graphZ (graphY c)) hζd ((hcYY (1, 0) (0, 1)).differentiableAt le_rfl),
      pull_T (c := graphY (graphZ c)) hζd ((hcYY (0, 1) (1, 0)).differentiableAt le_rfl),
      pull_T (c := graphZ (graphZ c)) hζd ((hcYY (0, 1) (0, 1)).differentiableAt le_rfl)]
    rw [hyzz, show seedPullback ζ (graphY (graphY (graphZ c))) p = _ from hfirst_swap (1, 0),
      show seedPullback ζ (graphZ (graphY (graphZ c))) p = _ from hfirst_swap (0, 1),
      hyzy]
    simp only [graphY, graphZ] at hyzy ⊢
    rw [hyzy]
    ring


private theorem near_STT {ζ : ℝ → ℝ} {c : GraphPlane → ℝ} {p : GraphPlane}
    (hζ : ContDiffAt ℝ 2 ζ p.1) (hc : ContDiffAt ℝ 2 c (seedPoint ζ p)) :
    T (T (seedPullback ζ c)) =ᶠ[𝓝 p] seedPullback ζ (graphY (graphY c)) := by
  filter_upwards
    [((continuous_fst : Continuous (Prod.fst : GraphPlane → ℝ)).continuousAt.tendsto.eventually
      (hζ.eventually (by simp))),
     ((seedPoint_smooth hζ).continuousAt.tendsto.eventually (hc.eventually (by simp)))]
    with q hqζ hqc
  exact (seed_mixed hqζ hqc).2

/-- The ordinary third graph-row identity, including the term that would survive
at a non-normalized endpoint. -/
theorem curved_seed_chain_rule {ζ : ℝ → ℝ} {c : GraphPlane → ℝ} {p : GraphPlane}
    (hζ : ContDiffAt ℝ 3 ζ p.1) (hc : ContDiffAt ℝ 3 c (seedPoint ζ p)) :
    let β := seedSlope ζ p
    let a := seedCurvature ζ p
    let C := seedPullback ζ c
    graphZ (graphY c) (seedPoint ζ p) = S (T C) p - β * T (T C) p ∧
    S (S (S C)) p - 3 * β * T (S (S C)) p +
        3 * β ^ 2 * S (T (T C)) p - β ^ 3 * T (T (T C)) p =
      graphZ (graphZ (graphZ c)) (seedPoint ζ p) +
        3 * a * graphZ (graphY c) (seedPoint ζ p) +
        S (seedCurvature ζ) p * graphY c (seedPoint ζ p) := by
  dsimp only
  have hζ₂ := hζ.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  have hc₂ := hc.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  have hζd := hζ.differentiableAt (by decide)
  obtain ⟨hm, htt⟩ := seed_mixed hζ₂ hc₂
  obtain ⟨hsss, hsst⟩ := third_rows hζ hc
  have hYY : DifferentiableAt ℝ (graphY (graphY c)) (seedPoint ζ p) := by
    have hY : ContDiffAt ℝ 2 (graphY c) (seedPoint ζ p) := partial_smooth (by simpa using hc)
    exact (partial_smooth (u := (1, 0)) (n := 1) (by simpa using hY)).differentiableAt le_rfl
  constructor
  · rw [hm, htt]
    unfold seedPullback
    ring
  · rw [hsss, hsst]
    have h1 := partial_congr (u := (1, 0)) (near_STT hζ₂ hc₂)
    have h2 := partial_congr (u := (0, 1)) (near_STT hζ₂ hc₂)
    change S (T (T (seedPullback ζ c))) p = S (seedPullback ζ (graphY (graphY c))) p at h1
    change T (T (T (seedPullback ζ c))) p = T (seedPullback ζ (graphY (graphY c))) p at h2
    rw [h1, h2, pull_S hζd hYY, pull_T hζd hYY]
    unfold seedPullback
    ring


/-- II4362–4366 at an actual normalized endpoint. The vanishing of the first
graph derivative in the y direction removes the third seed derivative. -/
theorem normalized_seed_rows {ζ : ℝ → ℝ} {c d : GraphPlane → ℝ}
    (hζ₀ : ζ 0 = 0) (hζ : ContDiffAt ℝ 3 ζ 0)
    (hc : ContDiffAt ℝ 3 c 0) (hd : DifferentiableAt ℝ d 0) (hd₀ : d 0 = 0)
    (hcy : graphY c 0 = 0)
    (hnull : (fun q => graphZ (graphZ c) q + 2 * d q * graphZ (graphY c) q +
      d q ^ 2 * graphY (graphY c) q) =ᶠ[𝓝 0] 0) :
    let β := seedSlope ζ 0
    let a := seedCurvature ζ 0
    let C := seedPullback ζ c
    let B := graphZ (graphY c) 0
    B = S (T C) 0 - β * T (T C) 0 ∧
    2 * B * nullRate d 0 = 3 * a * B -
      (S (S (S C)) 0 - 3 * β * T (S (S C)) 0 +
        3 * β ^ 2 * S (T (T C)) 0 - β ^ 3 * T (T (T C)) 0) := by
  have hp : seedPoint ζ 0 = 0 := by simp [seedPoint, hζ₀]
  have hc' : ContDiffAt ℝ 3 c (seedPoint ζ 0) := by rw [hp]; exact hc
  have h := curved_seed_chain_rule (ζ := ζ) (c := c) (p := 0) hζ hc'
  rw [hp] at h
  dsimp only at h ⊢
  refine ⟨h.1, ?_⟩
  rw [h.2, hcy, mul_zero, add_zero]
  linarith only [ordinary_graph_row hc hd hd₀ hnull]

/-- The retained graph rows that enter the change of the pure third output. -/
abbrev SeedRows (ι : Type*) := ι × ι × ι × ι × ι

abbrev SeedRows.st {ι : Type*} (r : SeedRows ι) : ι := r.1
abbrev SeedRows.tt {ι : Type*} (r : SeedRows ι) : ι := r.2.1
abbrev SeedRows.sst {ι : Type*} (r : SeedRows ι) : ι := r.2.2.1
abbrev SeedRows.stt {ι : Type*} (r : SeedRows ι) : ι := r.2.2.2.1
abbrev SeedRows.ttt {ι : Type*} (r : SeedRows ι) : ι := r.2.2.2.2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def retainedMixed (r : SeedRows ι) (β : ℝ) (w : ι → ℝ) : ℝ :=
  w r.st - β * w r.tt

def retainedThird (r : SeedRows ι) (β a : ℝ) (w : ι → ℝ) : ℝ :=
  3 * a * retainedMixed r β w + 3 * β * w r.sst -
    3 * β ^ 2 * w r.stt + β ^ 3 * w r.ttt

omit [Fintype ι] in
private theorem no_pure_row (r : SeedRows ι) (j : ι)
    (hrows : r.st ≠ j ∧ r.tt ≠ j ∧ r.sst ≠ j ∧ r.stt ≠ j ∧ r.ttt ≠ j)
    (β a v : ℝ) (w : ι → ℝ) :
    retainedMixed r β (Function.update w j v) = retainedMixed r β w ∧
    retainedThird r β a (Function.update w j v) = retainedThird r β a w := by
  simp [retainedThird, retainedMixed, hrows.1, hrows.2.1, hrows.2.2.1, hrows.2.2.2.1,
    hrows.2.2.2.2]

private theorem atlas_row {F : (ι → ℝ) → (ι → ℝ)} {p : ι → ℝ}
    (hF : DifferentiableAt ℝ F p) (i : ι) :
    ordinaryJacobian F p i = fun k => fderiv ℝ (fun q => F q i) p (Pi.single k 1) := by
  have h := (hasFDerivAt_pi'.1 hF.hasFDerivAt i).fderiv
  ext k
  rw [h]
  rfl

private theorem det_row_replacement_sum (M : Matrix ι ι ℝ) (j : ι)
    {a : ℝ} {u : ι → ℝ} (hu : u j = 0) :
    (M.updateRow j (a • M j + ∑ i, u i • M i)).det = a * M.det := by
  rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    Matrix.det_updateRow_sum, hu, zero_smul, add_zero]

private theorem det_curved_restore {F G : (ι → ℝ) → (ι → ℝ)} {p : ι → ℝ}
    (r : SeedRows ι) (j : ι) (β a κ : ℝ)
    (hrows : r.st ≠ j ∧ r.tt ≠ j ∧ r.sst ≠ j ∧ r.stt ≠ j ∧ r.ttt ≠ j)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p)
    (hrestore : F =ᶠ[𝓝 p] fun q => Function.update (G q) j
      (κ * (retainedThird r β a (G q) - 2 * retainedMixed r β (G q) * G q j))) :
    (ordinaryJacobian F p).det =
      (κ * (-(2 * retainedMixed r β (G p)))) * (ordinaryJacobian G p).det := by
  let J := ordinaryJacobian G p
  let A := κ * (-(2 * retainedMixed r β (G p)))
  let w := fun i => κ * (3 * a - 2 * G p j) *
        ((if i = r.st then 1 else 0) + if i = r.tt then -β else 0) +
      κ * ((if i = r.sst then 3 * β else 0) +
        (if i = r.stt then -(3 * β ^ 2) else 0) + if i = r.ttt then β ^ 3 else 0)
  have hw : w j = 0 := by
    simp [w, Ne.symm hrows.1, Ne.symm hrows.2.1, Ne.symm hrows.2.2.1,
      Ne.symm hrows.2.2.2.1, Ne.symm hrows.2.2.2.2]
  have hm : ordinaryJacobian F p = J.updateRow j (A • J j + ∑ i, w i • J i) := by
    ext i k
    by_cases hi : i = j
    · subst i
      have hrow (i : ι) := hasFDerivAt_pi'.1 hG.hasFDerivAt i
      have hm := (hrow r.st).sub ((hrow r.tt).const_mul β)
      have hthird := (((hm.const_mul (3 * a)).add ((hrow r.sst).const_mul (3 * β))).sub
        ((hrow r.stt).const_mul (3 * β ^ 2))).add ((hrow r.ttt).const_mul (β ^ 3))
      have h := (hthird.sub ((hm.const_mul 2).mul (hrow j))).const_mul κ
      have hlocal : (fun q => F q j) =ᶠ[𝓝 p] (fun q =>
          κ * (retainedThird r β a (G q) - 2 * retainedMixed r β (G q) * G q j)) := by
        filter_upwards [hrestore] with q hq
        simp [hq]
      rw [atlas_row hF, Matrix.updateRow_self, (h.congr_of_eventuallyEq hlocal).fderiv]
      simp only [J, A, ordinaryJacobian, w, retainedMixed, retainedThird,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
      simp only [mul_add, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite,
        zero_mul, mul_zero, one_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      ring
    · have heq : (fun q => F q i) =ᶠ[𝓝 p] (fun q => G q i) := by
        filter_upwards [hrestore] with q hq
        simp [hq, hi]
      rw [atlas_row hF, Matrix.updateRow_ne hi,
        ((hasFDerivAt_pi'.1 hG.hasFDerivAt i).congr_of_eventuallyEq heq).fderiv]
      rfl
  rw [hm, det_row_replacement_sum J j hw]

/-- Actual rate atlas in the same coefficient frame. -/
noncomputable def curvedRateAtlas (j : ι) (F : (ι → ℝ) → (ι → ℝ))
    (d : (ι → ℝ) → GraphPlane → ℝ) (p : ι → ℝ) : ι → ℝ :=
  actualRateAtlas j F d (fun _ => 0) p

/-- II4368 for an actual normalized seed atlas. The ordinary convention uses
`κ=1`; the Taylor convention uses `κ=1/6` only on the replaced row. -/
theorem curved_seed_atlas {ζ : ℝ → ℝ} (hζ₀ : ζ 0 = 0) (hζ : ContDiffAt ℝ 3 ζ 0)
    (r : SeedRows ι) (j : ι)
    (hrows : r.st ≠ j ∧ r.tt ≠ j ∧ r.sst ≠ j ∧ r.stt ≠ j ∧ r.ttt ≠ j)
    {κ : ℝ} (hκ : 0 < κ) {U : Set (ι → ℝ)} (hU : IsOpen U)
    {F : (ι → ℝ) → (ι → ℝ)} {c d : (ι → ℝ) → GraphPlane → ℝ}
    (hF : ∀ p ∈ U, DifferentiableAt ℝ F p)
    (hc : ∀ p ∈ U, ContDiffAt ℝ 3 (c p) 0)
    (hd : ∀ p ∈ U, DifferentiableAt ℝ (d p) 0)
    (hd₀ : ∀ p ∈ U, d p 0 = 0)
    (hcy : ∀ p ∈ U, graphY (c p) 0 = 0)
    (hnull : ∀ p ∈ U, (fun q => graphZ (graphZ (c p)) q +
      2 * d p q * graphZ (graphY (c p)) q + d p q ^ 2 * graphY (graphY (c p)) q)
        =ᶠ[𝓝 0] 0)
    (hB : ∀ p ∈ U, graphZ (graphY (c p)) 0 ≠ 0)
    (hjet : ∀ p ∈ U,
      let C := seedPullback ζ (c p)
      F p r.st = S (T C) 0 ∧ F p r.tt = T (T C) 0 ∧
      F p r.sst = T (S (S C)) 0 ∧ F p r.stt = S (T (T C)) 0 ∧
      F p r.ttt = T (T (T C)) 0 ∧ F p j = κ * S (S (S C)) 0) :
    ∀ p ∈ U,
      let G := curvedRateAtlas j F d
      let B := graphZ (graphY (c p)) 0
      DifferentiableAt ℝ G p ∧
      (ordinaryJacobian G p).det = -(κ * (2 * B))⁻¹ * (ordinaryJacobian F p).det ∧
      |(ordinaryJacobian G p).det|⁻¹ =
        (κ * (2 * |B|)) * |(ordinaryJacobian F p).det|⁻¹ := by
  intro p hp
  dsimp only
  let β := seedSlope ζ 0
  let a := seedCurvature ζ 0
  let G := curvedRateAtlas j F d
  have heq (q : ι → ℝ) (hq : q ∈ U) :
      retainedMixed r β (F q) = graphZ (graphY (c q)) 0 ∧
      2 * retainedMixed r β (F q) * nullRate (d q) 0 =
        retainedThird r β a (F q) - F q j / κ := by
    obtain ⟨hst, htt, hsst, hstt, httt, hsss⟩ := hjet q hq
    have h := normalized_seed_rows hζ₀ hζ (hc q hq) (hd q hq) (hd₀ q hq) (hcy q hq) (hnull q hq)
    dsimp only at h
    have hmix : retainedMixed r β (F q) = graphZ (graphY (c q)) 0 := by
      rw [retainedMixed, hst, htt, h.1]
    refine ⟨hmix, ?_⟩
    rw [hmix, h.2, retainedThird, hmix, hsst, hstt, httt, hsss]
    field_simp
    ring
  have hrate (q : ι → ℝ) (hq : q ∈ U) :
      nullRate (d q) 0 =
        (retainedThird r β a (F q) - F q j / κ) / (2 * retainedMixed r β (F q)) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero ((heq q hq).1 ▸ hB q hq))]
    linarith only [(heq q hq).2]
  have hnear : (fun q => nullRate (d q) 0) =ᶠ[𝓝 p] fun q =>
      (retainedThird r β a (F q) - F q j / κ) / (2 * retainedMixed r β (F q)) :=
    by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hrate q hq
  have hdiff (i : ι) := differentiableAt_pi.1 (hF p hp) i
  have hm : DifferentiableAt ℝ (fun q => retainedMixed r β (F q)) p :=
    (hdiff r.st).sub ((hdiff r.tt).const_mul β)
  have ht : DifferentiableAt ℝ (fun q => retainedThird r β a (F q)) p :=
    (((hm.const_mul (3 * a)).add ((hdiff r.sst).const_mul (3 * β))).sub
      ((hdiff r.stt).const_mul (3 * β ^ 2))).add ((hdiff r.ttt).const_mul (β ^ 3))
  have hden : DifferentiableAt ℝ (fun q => 2 * retainedMixed r β (F q)) p := hm.const_mul 2
  have hj : DifferentiableAt ℝ (fun q => F q j / κ) p := by
    simpa only [div_eq_mul_inv] using (hdiff j).mul_const κ⁻¹
  have hdiv := (ht.sub hj).mul
    (hden.inv (mul_ne_zero two_ne_zero ((heq p hp).1 ▸ hB p hp)))
  have hv : DifferentiableAt ℝ (fun q => nullRate (d q) 0) p := by
    apply DifferentiableAt.congr_of_eventuallyEq _ hnear
    simpa only [div_eq_mul_inv] using hdiv
  have hG : DifferentiableAt ℝ G p := by
    apply differentiableAt_pi.2
    intro i
    by_cases hi : i = j
    · subst i
      simpa [G, curvedRateAtlas, actualRateAtlas] using hv
    · simpa [G, curvedRateAtlas, actualRateAtlas, hi] using hdiff i
  have hrestore : F =ᶠ[𝓝 p] fun q => Function.update (G q) j
      (κ * (retainedThird r β a (G q) - 2 * retainedMixed r β (G q) * G q j)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    have hh := no_pure_row r j hrows β a (nullRate (d q) 0) (F q)
    ext i
    by_cases hi : i = j
    · subst i
      simp only [G, curvedRateAtlas, actualRateAtlas, Function.update_self, hh.1, hh.2]
      have h := (heq q hq).2
      field_simp at h
      nlinarith only [h]
    · simp [G, curvedRateAtlas, actualRateAtlas, hi]
  have hd := det_curved_restore r j β a κ hrows (hF p hp) hG hrestore
  have hBm : retainedMixed r β (G p) = graphZ (graphY (c p)) 0 :=
    (no_pure_row r j hrows β a (nullRate (d p) 0) (F p)).1.trans (heq p hp).1
  rw [hBm] at hd
  refine ⟨hG, ?_, ?_⟩
  · rw [hd]
    field_simp [ne_of_gt hκ, hB p hp]; ring
  · rw [hd, abs_mul, abs_mul, abs_neg, abs_mul, abs_of_pos hκ, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [← mul_assoc, mul_inv]
    symm
    exact mul_inv_cancel_left₀ (mul_ne_zero (mul_ne_zero (ne_of_gt hκ) two_ne_zero)
      (abs_ne_zero.mpr (hB p hp))) _


/-- The manuscript's pure third graph row in ordinary and Taylor coordinates. -/
theorem curved_seed_inverse_densities {ζ : ℝ → ℝ} (hζ₀ : ζ 0 = 0)
    (hζ : ContDiffAt ℝ 3 ζ 0) (r : SeedRows ι) (j : ι)
    (hrows : r.st ≠ j ∧ r.tt ≠ j ∧ r.sst ≠ j ∧ r.stt ≠ j ∧ r.ttt ≠ j)
    {U : Set (ι → ℝ)} (hU : IsOpen U)
    {F : (ι → ℝ) → (ι → ℝ)} {c d : (ι → ℝ) → GraphPlane → ℝ}
    (hF : ∀ p ∈ U, DifferentiableAt ℝ F p)
    (hc : ∀ p ∈ U, ContDiffAt ℝ 3 (c p) 0)
    (hd : ∀ p ∈ U, DifferentiableAt ℝ (d p) 0)
    (hd₀ : ∀ p ∈ U, d p 0 = 0)
    (hcy : ∀ p ∈ U, graphY (c p) 0 = 0)
    (hnull : ∀ p ∈ U, (fun q => graphZ (graphZ (c p)) q +
      2 * d p q * graphZ (graphY (c p)) q + d p q ^ 2 * graphY (graphY (c p)) q)
        =ᶠ[𝓝 0] 0)
    (hB : ∀ p ∈ U, graphZ (graphY (c p)) 0 ≠ 0)
    (hjet : ∀ p ∈ U,
      let C := seedPullback ζ (c p)
      F p r.st = S (T C) 0 ∧ F p r.tt = T (T C) 0 ∧
      F p r.sst = T (S (S C)) 0 ∧ F p r.stt = S (T (T C)) 0 ∧
      F p r.ttt = T (T (T C)) 0 ∧ F p j = S (S (S C)) 0) :
    ∀ p ∈ U,
      let C := seedPullback ζ (c p)
      let β := seedSlope ζ 0
      let a := seedCurvature ζ 0
      let B := graphZ (graphY (c p)) 0
      let G := curvedRateAtlas j F d
      let F_T := fun q => Function.update (F q) j (F q j / 6)
      B = S (T C) 0 - β * T (T C) 0 ∧
      2 * B * nullRate (d p) 0 = 3 * a * B -
        (S (S (S C)) 0 - 3 * β * T (S (S C)) 0 +
          3 * β ^ 2 * S (T (T C)) 0 - β ^ 3 * T (T (T C)) 0) ∧
      (ordinaryJacobian G p).det = -(2 * B)⁻¹ * (ordinaryJacobian F p).det ∧
      |(ordinaryJacobian G p).det|⁻¹ = (2 * |B|) * |(ordinaryJacobian F p).det|⁻¹ ∧
      |(ordinaryJacobian G p).det|⁻¹ = (|B| / 3) * |(ordinaryJacobian F_T p).det|⁻¹ := by
  let F_T := fun q : ι → ℝ => Function.update (F q) j (F q j / 6)
  have hTF (p) (hp : p ∈ U) : DifferentiableAt ℝ F_T p := by
    apply differentiableAt_pi.2
    intro i
    have hfi := differentiableAt_pi.1 (hF p hp) i
    by_cases hi : i = j
    · subst i
      simpa [F_T, div_eq_mul_inv] using hfi.mul_const (6 : ℝ)⁻¹
    · simpa [F_T, hi] using hfi
  have hOrd := curved_seed_atlas hζ₀ hζ r j hrows (κ := 1) (by norm_num)
    hU hF hc hd hd₀ hcy hnull hB (by simpa using hjet)
  have hT := curved_seed_atlas hζ₀ hζ r j hrows (κ := 1 / 6) (by norm_num)
    hU hTF hc hd hd₀ hcy hnull hB (by
      intro p hp
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hjet p hp
      simp only [F_T, Function.update_of_ne hrows.1, Function.update_of_ne hrows.2.1,
        Function.update_of_ne hrows.2.2.1, Function.update_of_ne hrows.2.2.2.1,
        Function.update_of_ne hrows.2.2.2.2, Function.update_self]
      refine ⟨h₁, h₂, h₃, h₄, h₅, ?_⟩
      rw [h₆]
      ring)
  intro p hp
  have hG : curvedRateAtlas j F_T d = curvedRateAtlas j F d := by
    funext q
    simp [F_T, curvedRateAtlas, actualRateAtlas]
  have hRows := normalized_seed_rows hζ₀ hζ (hc p hp) (hd p hp) (hd₀ p hp) (hcy p hp) (hnull p hp)
  obtain ⟨_, h1, h2⟩ := hOrd p hp
  obtain ⟨_, _, h3⟩ := hT p hp
  simp only [hG] at h3
  refine ⟨hRows.1, hRows.2, ?_, ?_, ?_⟩
  · simpa using h1
  · simpa using h2
  · convert h3 using 2; ring

end PaperII.PreparedCurvedSeed
