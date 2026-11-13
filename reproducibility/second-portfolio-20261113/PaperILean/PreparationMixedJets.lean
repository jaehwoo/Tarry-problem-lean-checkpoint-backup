import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Actual coordinate derivatives used in the rectangle preparation lemma.
Smoothness is required only on the open domain; no smooth extension is assumed.
The order `∞` means smooth in the pinned Mathlib, whereas `⊤` would mean analytic. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

namespace PaperI.Preparation

def derivX (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => f (x, p.2)) p.1

def derivY (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => f (p.1, y)) p.2

def horizontalJet (f : ℝ × ℝ → ℝ) (a : ℕ) : ℝ × ℝ → ℝ :=
  derivX^[a] f

def mixedJet (f : ℝ × ℝ → ℝ) (a b : ℕ) : ℝ × ℝ → ℝ :=
  derivY^[b] (horizontalJet f a)

@[simp] theorem horizontalJet_zero (f : ℝ × ℝ → ℝ) : horizontalJet f 0 = f := rfl

@[simp] theorem mixedJet_zero_right (f : ℝ × ℝ → ℝ) (a : ℕ) :
    mixedJet f a 0 = horizontalJet f a := rfl

@[simp] theorem mixedJet_zero_zero (f : ℝ × ℝ → ℝ) : mixedJet f 0 0 = f := rfl

theorem horizontalJet_succ (f : ℝ × ℝ → ℝ) (a : ℕ) :
    horizontalJet f (a + 1) = derivX (horizontalJet f a) :=
  Function.iterate_succ_apply' _ _ _

theorem mixedJet_succ_right (f : ℝ × ℝ → ℝ) (a b : ℕ) :
    mixedJet f a (b + 1) = derivY (mixedJet f a b) :=
  Function.iterate_succ_apply' _ _ _

theorem horizontalJet_eq_iteratedDeriv (f : ℝ × ℝ → ℝ) (a : ℕ) (p : ℝ × ℝ) :
    horizontalJet f a p = iteratedDeriv a (fun x => f (x, p.2)) p.1 := by
  induction a generalizing p with
  | zero => simp
  | succ a ih =>
    rw [horizontalJet_succ, derivX, iteratedDeriv_succ]
    congr 1
    funext x
    exact ih (x, p.2)

theorem mixedJet_eq_iteratedDeriv (f : ℝ × ℝ → ℝ) (a b : ℕ) (p : ℝ × ℝ) :
    mixedJet f a b p =
      iteratedDeriv b (fun y => horizontalJet f a (p.1, y)) p.2 := by
  induction b generalizing p with
  | zero => simp
  | succ b ih =>
    rw [mixedJet_succ_right, derivY, iteratedDeriv_succ]
    congr 1
    funext y
    exact ih (p.1, y)

theorem contDiffAt_derivX {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ ∞ f p) : ContDiffAt ℝ ∞ (derivX f) p := by
  have hh : ContDiffAt ℝ ∞
      (fun q : (ℝ × ℝ) × ℝ => f (q.2, q.1.2)) (p, p.1) :=
    hf.comp (p, p.1)
      (contDiffAt_snd.prodMk (contDiffAt_snd.comp (p, p.1) contDiffAt_fst))
  have hd : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => fderiv ℝ (fun x => f (x, q.2)) q.1) p :=
    hh.fderiv contDiffAt_fst (by simp)
  exact hd.clm_apply contDiffAt_const

theorem contDiffAt_derivY {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ ∞ f p) : ContDiffAt ℝ ∞ (derivY f) p := by
  have hh : ContDiffAt ℝ ∞
      (fun q : (ℝ × ℝ) × ℝ => f (q.1.1, q.2)) (p, p.2) :=
    hf.comp (p, p.2)
      ((contDiffAt_fst.comp (p, p.2) contDiffAt_fst).prodMk contDiffAt_snd)
  have hd : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => fderiv ℝ (fun y => f (q.1, y)) q.2) p :=
    hh.fderiv contDiffAt_snd (by simp)
  exact hd.clm_apply contDiffAt_const

theorem contDiffOn_derivX {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) : ContDiffOn ℝ ∞ (derivX f) s := by
  intro p hp
  exact (contDiffAt_derivX (hf.contDiffAt (hs.mem_nhds hp))).contDiffWithinAt

theorem contDiffOn_derivY {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) : ContDiffOn ℝ ∞ (derivY f) s := by
  intro p hp
  exact (contDiffAt_derivY (hf.contDiffAt (hs.mem_nhds hp))).contDiffWithinAt

theorem contDiffOn_horizontalJet {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (a : ℕ) :
    ContDiffOn ℝ ∞ (horizontalJet f a) s := by
  induction a with
  | zero => exact hf
  | succ a ih => rw [horizontalJet_succ]; exact contDiffOn_derivX hs ih

theorem contDiffOn_mixedJet {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (a b : ℕ) :
    ContDiffOn ℝ ∞ (mixedJet f a b) s := by
  induction b with
  | zero => exact contDiffOn_horizontalJet hs hf a
  | succ b ih => rw [mixedJet_succ_right]; exact contDiffOn_derivY hs ih

theorem continuousOn_horizontalJet {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (a : ℕ) :
    ContinuousOn (horizontalJet f a) s := (contDiffOn_horizontalJet hs hf a).continuousOn

theorem continuousOn_mixedJet {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (a b : ℕ) :
    ContinuousOn (mixedJet f a b) s := (contDiffOn_mixedJet hs hf a b).continuousOn

theorem measurable_mixedJet_restrict {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (a b : ℕ) :
    Measurable (fun p : s => mixedJet f a b p) :=
  (continuousOn_iff_continuous_restrict.mp (continuousOn_mixedJet hs hf a b)).measurable

theorem aemeasurable_mixedJet {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (a b : ℕ) :
    AEMeasurable (mixedJet f a b) (volume.restrict s) :=
  (continuousOn_mixedJet hs hf a b).aemeasurable hs.measurableSet

theorem contDiffOn_sectionX {f : ℝ × ℝ → ℝ} {x0 x1 y0 y1 y : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo x0 x1 ×ˢ Ioo y0 y1)) (hy : y ∈ Ioo y0 y1) :
    ContDiffOn ℝ ∞ (fun x => f (x, y)) (Ioo x0 x1) :=
  hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx => ⟨hx, hy⟩)

theorem contDiffOn_sectionY {f : ℝ × ℝ → ℝ} {x0 x1 y0 y1 x : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo x0 x1 ×ˢ Ioo y0 y1)) (hx : x ∈ Ioo x0 x1) :
    ContDiffOn ℝ ∞ (fun y => f (x, y)) (Ioo y0 y1) :=
  hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨hx, hy⟩)

private theorem iteratedDeriv_zero_function (n : ℕ) :
    iteratedDeriv n (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iteratedDeriv_succ, ih]; exact deriv_const' (𝕜 := ℝ) (c := (0 : ℝ))

theorem horizontalJet_eq_zero_of_eq_zero {f : ℝ × ℝ → ℝ} {x0 x1 y0 y1 : ℝ}
    (hzero : ∀ p ∈ Ioo x0 x1 ×ˢ Ioo y0 y1, f p = 0) (a : ℕ)
    {p : ℝ × ℝ} (hp : p ∈ Ioo x0 x1 ×ˢ Ioo y0 y1) : horizontalJet f a p = 0 := by
  rw [horizontalJet_eq_iteratedDeriv]
  have he : EqOn (fun x => f (x, p.2)) (fun _ => 0) (Ioo x0 x1) :=
    fun x hx => hzero (x, p.2) ⟨hx, hp.2⟩
  have hi := he.iteratedDeriv_of_isOpen isOpen_Ioo a hp.1
  simpa only [iteratedDeriv_zero_function] using hi

theorem mixedJet_eq_zero_of_eq_zero {f : ℝ × ℝ → ℝ} {x0 x1 y0 y1 : ℝ}
    (hzero : ∀ p ∈ Ioo x0 x1 ×ˢ Ioo y0 y1, f p = 0) (a b : ℕ)
    {p : ℝ × ℝ} (hp : p ∈ Ioo x0 x1 ×ˢ Ioo y0 y1) : mixedJet f a b p = 0 := by
  rw [mixedJet_eq_iteratedDeriv]
  have he : EqOn (fun y => horizontalJet f a (p.1, y)) (fun _ => 0) (Ioo y0 y1) :=
    fun _ hy => horizontalJet_eq_zero_of_eq_zero hzero a ⟨hp.1, hy⟩
  have hi := he.iteratedDeriv_of_isOpen isOpen_Ioo b hp.2
  simpa only [iteratedDeriv_zero_function] using hi

theorem mixedJet_eq_zero_of_amplitude_zero {f : ℝ × ℝ → ℝ} {x0 x1 y0 y1 : ℝ}
    (hamp : ∀ p ∈ Ioo x0 x1 ×ˢ Ioo y0 y1, |f p| ≤ 0) (a b : ℕ)
    {p : ℝ × ℝ} (hp : p ∈ Ioo x0 x1 ×ˢ Ioo y0 y1) : mixedJet f a b p = 0 := by
  apply mixedJet_eq_zero_of_eq_zero (a := a) (b := b) (hp := hp)
  intro q hq
  exact abs_nonpos_iff.mp (hamp q hq)

end PaperI.Preparation
