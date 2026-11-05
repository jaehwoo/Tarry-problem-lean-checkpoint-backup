import PaperILean.OriginalUpperNormalPullback
import Mathlib.MeasureTheory.Measure.Prod

/-! The arbitrary-polynomial and constant-representative application in the
whole conditional Haar lemma. An invertible original affine frame turns ONE
nonempty orbit-window witness into a bounded-degree coefficient representative
of the original phase modulo its constant. No truncation or degree hypothesis
is imposed. The stronger function formulation includes every polynomial. -/
noncomputable section
namespace PaperI.OriginalHaarArbitraryPhase
open Set MeasureTheory
open scoped ENNReal

abbrev Upper := Fin 6 → ℝ

def normalizedAlong (f : PhysicalSpace → ℝ) (g : Upper) (x : PhysicalSpace) : ℝ :=
  f (originalUpperAffineEval g x) - f (originalUpperAffineEval g 0)

def rawOrbitSet {k : ℕ} (K : Set Upper) (W : Set (CoefficientSpace k))
    (f : PhysicalSpace → ℝ) : Set Upper :=
  {g | g ∈ K ∧ ∃ F ∈ W, ∀ x : PhysicalSpace, phase F x = normalizedAlong f g x}

def coefficientOrbitSet {k : ℕ} (K : Set Upper) (W : Set (CoefficientSpace k))
    (F : CoefficientSpace k) : Set Upper :=
  {g | g ∈ K ∧ originalUpperCoefficientPullback F g ∈ W}

theorem phase_pullback_normalized {k : ℕ} (F : CoefficientSpace k) (g : Upper)
    (x : PhysicalSpace) :
    phase (originalUpperCoefficientPullback F g) x = normalizedAlong (phase F) g x := by
  simpa [normalizedAlong,originalUpperAffineEval] using
    originalUpperCoefficientPullback_phase F g x

theorem eval_frame_inverse (g : Upper) (x : PhysicalSpace) :
    originalUpperAffineEval g (originalUpperAffineEval (originalUpperAffineInv g) x) = x := by
  rw [← originalUpperAffineEval_comp, (originalUpperAffineComp_inv g).2]
  ext i
  fin_cases i <;> simp [originalUpperAffineEval]

/-- The witness's inverse affine pullback represents the ENTIRE original
function modulo its one constant, not a coefficient truncation of it. -/
theorem representative_from_one_witness {k : ℕ} (f : PhysicalSpace → ℝ)
    (g : Upper) (F : CoefficientSpace k)
    (hF : ∀ x : PhysicalSpace, phase F x = normalizedAlong f g x) :
    ∀ x : PhysicalSpace,
      phase (originalUpperCoefficientPullback F (originalUpperAffineInv g)) x = f x - f 0 := by
  intro x
  rw [phase_pullback_normalized]
  unfold normalizedAlong
  rw [hF,hF]
  unfold normalizedAlong
  rw [eval_frame_inverse,eval_frame_inverse]
  ring

theorem normalizedAlong_eq_of_representative {k : ℕ} (f : PhysicalSpace → ℝ)
    (F : CoefficientSpace k) (hF : ∀ x : PhysicalSpace, phase F x = f x - f 0)
    (g : Upper) (x : PhysicalSpace) :
    normalizedAlong (phase F) g x = normalizedAlong f g x := by
  unfold normalizedAlong
  rw [hF,hF]
  ring

theorem rawOrbitSet_eq_of_representative {k : ℕ} (K : Set Upper)
    (W : Set (CoefficientSpace k)) (f : PhysicalSpace → ℝ) (F : CoefficientSpace k)
    (hF : ∀ x : PhysicalSpace, phase F x = f x - f 0) :
    rawOrbitSet K W f = coefficientOrbitSet K W F := by
  ext g
  constructor
  · rintro ⟨hg,G,hG,hphase⟩
    refine ⟨hg,?_⟩
    have heq : G = originalUpperCoefficientPullback F g := by
      apply coefficient_ext
      intro x
      rw [hphase,phase_pullback_normalized,normalizedAlong_eq_of_representative f F hF]
    simpa only [← heq] using hG
  · rintro ⟨hg,hW⟩
    refine ⟨hg,originalUpperCoefficientPullback F g,hW,?_⟩
    intro x
    rw [phase_pullback_normalized,normalizedAlong_eq_of_representative f F hF]

/-- If no bounded-degree representative exists, the original orbit window is
empty. This includes arbitrary polynomials whose nonconstant degree exceeds k. -/
theorem rawOrbitSet_empty_of_no_representative {k : ℕ} (K : Set Upper)
    (W : Set (CoefficientSpace k)) (f : PhysicalSpace → ℝ)
    (h : ¬ ∃ F : CoefficientSpace k, ∀ x : PhysicalSpace, phase F x = f x - f 0) :
    rawOrbitSet K W f = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  rintro g ⟨_,F,_,hF⟩
  exact h ⟨_,representative_from_one_witness f g F hF⟩

/-- Exact application bridge: a proved coefficient-seed bound extends to the
original unrestricted phase quantifier, without a new degree or norm premise.
The coefficient bound remains explicit until the full Haar lemma supplies it. -/
theorem arbitrary_phase_bound_of_coefficient_bound {k : ℕ}
    (K : Set Upper) (W : Set (CoefficientSpace k)) (μ : Measure Upper) (B : ℝ≥0∞)
    (hbound : ∀ F : CoefficientSpace k, μ (coefficientOrbitSet K W F) ≤ B)
    (f : PhysicalSpace → ℝ) : μ (rawOrbitSet K W f) ≤ B := by
  classical
  by_cases h : (rawOrbitSet K W f).Nonempty
  · obtain ⟨g,_,F,hFW,hF⟩ := h
    let F₀ := originalUpperCoefficientPullback F (originalUpperAffineInv g)
    have hrep : ∀ x : PhysicalSpace, phase F₀ x = f x - f 0 :=
      representative_from_one_witness f g F hF
    rw [rawOrbitSet_eq_of_representative K W f F₀ hrep]
    exact hbound F₀
  · rw [Set.not_nonempty_iff_eq_empty.mp h,measure_empty]
    exact bot_le

theorem normalizedAlong_left_coset (f : PhysicalSpace → ℝ) (g₀ g : Upper)
    (x : PhysicalSpace) :
    normalizedAlong (f ∘ originalUpperAffineEval g₀) g x =
      normalizedAlong f (originalUpperAffineComp g₀ g) x := by
  simp only [normalizedAlong,Function.comp_apply,originalUpperAffineEval_comp]

/-- The fixed left-coset location is absorbed into the unrestricted phase.
There is no coefficient/location bound on g₀. -/
theorem arbitrary_left_coset_bound_of_coefficient_bound {k : ℕ}
    (K : Set Upper) (W : Set (CoefficientSpace k)) (μ : Measure Upper) (B : ℝ≥0∞)
    (hbound : ∀ F : CoefficientSpace k, μ (coefficientOrbitSet K W F) ≤ B)
    (f : PhysicalSpace → ℝ) (g₀ : Upper) :
    μ {g | g ∈ K ∧ ∃ F ∈ W, ∀ x : PhysicalSpace,
      phase F x = normalizedAlong f (originalUpperAffineComp g₀ g) x} ≤ B := by
  simpa only [rawOrbitSet,normalizedAlong_left_coset] using
    arbitrary_phase_bound_of_coefficient_bound K W μ B hbound
      (f ∘ originalUpperAffineEval g₀)

end PaperI.OriginalHaarArbitraryPhase
