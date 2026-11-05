import PaperILean.I2385ProductHaar
import PaperILean.OriginalHaarWindowPieces

/-! The final finite-relative-box volume implication in the conditional Haar
lemma, using the source's actual coordinate Lebesgue Haar normalization. -/
noncomputable section
namespace PaperI.OriginalHaarWindowBoxes
open Set MeasureTheory
open I2385ProductHaar
open scoped ENNReal

abbrev Upper := Fin 6 → ℝ

def upperBox (R : ℝ) : Set Upper := {g | ‖g‖ ≤ R}

theorem measurableSet_upperBox (R : ℝ) : MeasurableSet (upperBox R) :=
  measurableSet_le measurable_norm measurable_const

def quadBox (R : ℝ) : Set Quad :=
  Icc (-R) R ×ˢ (Icc (-R) R ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))

def tripleBox (R : ℝ) : Set Triple :=
  Icc (-R) R ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)

theorem h0_preimage_upperBox (R : ℝ) :
    h0Coordinates ⁻¹' upperBox R = quadBox R := by
  ext p
  simp only [Set.mem_preimage,upperBox,Set.mem_setOf_eq,quadBox,Set.mem_prod,
    Set.mem_Icc]
  constructor
  · intro h
    have hb (i : Fin 6) : |h0Coordinates p i| ≤ R :=
      (norm_le_pi_norm _ i).trans h
    exact ⟨by simpa [h0Coordinates,abs_le] using hb 3,
      by simpa [h0Coordinates,abs_le] using hb 0,
      by simpa [h0Coordinates,abs_le] using hb 1,
      by simpa [h0Coordinates,abs_le] using hb 2⟩
  · rintro ⟨hd,ha,hb,hc⟩
    have hR : 0 ≤ R := by linarith [ha.1,ha.2]
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    fin_cases i <;> simp [h0Coordinates]
    · exact abs_le.mpr ha
    · exact abs_le.mpr hb
    · exact abs_le.mpr hc
    · exact abs_le.mpr hd
    all_goals exact hR

theorem h3_preimage_upperBox (R : ℝ) :
    h3Coordinates ⁻¹' upperBox R = tripleBox R := by
  ext p
  simp only [Set.mem_preimage,upperBox,Set.mem_setOf_eq,tripleBox,Set.mem_prod,
    Set.mem_Icc]
  constructor
  · intro h
    have hb (i : Fin 6) : |h3Coordinates p i| ≤ R :=
      (norm_le_pi_norm _ i).trans h
    exact ⟨by simpa [h3Coordinates,abs_le] using hb 0,
      by simpa [h3Coordinates,abs_le] using hb 1,
      by simpa [h3Coordinates,abs_le] using hb 2⟩
  · rintro ⟨ha,hb,hc⟩
    have hR : 0 ≤ R := by linarith [ha.1,ha.2]
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    fin_cases i <;> simp [h3Coordinates]
    · exact abs_le.mpr ha
    · exact abs_le.mpr hb
    · exact abs_le.mpr hc
    all_goals exact hR

theorem haar0_upperBox (R : ℝ) :
    haar0 (upperBox R) = ENNReal.ofReal (2*R)^4 := by
  rw [haar0,Measure.map_apply continuous_h0Coordinates.measurable (measurableSet_upperBox R),
    h0_preimage_upperBox]
  simp only [quadBox,Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Icc,sub_neg_eq_add]
  rw [← two_mul]
  ring

theorem haar3_upperBox (R : ℝ) :
    haar3 (upperBox R) = ENNReal.ofReal (2*R)^3 := by
  rw [haar3,Measure.map_apply continuous_h3Coordinates.measurable (measurableSet_upperBox R),
    h3_preimage_upperBox]
  simp only [tripleBox,Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Icc,sub_neg_eq_add]
  rw [← two_mul]
  ring

def inverse0 (g : Quad) : Quad :=
  (-g.1,(-g.2.1,(g.2.1*g.1-g.2.2.1,-g.2.2.2)))

theorem inverse0_coordinates (g : Quad) :
    originalUpperAffineInv (h0Coordinates g) = h0Coordinates (inverse0 g) := by
  ext i
  fin_cases i <;> simp [originalUpperAffineInv,h0Coordinates,inverse0]

theorem haar0_relative_invariant (g : Quad) :
    Measure.map (originalUpperRelativeFrame (h0Coordinates g)) haar0 = haar0 := by
  change Measure.map (originalUpperAffineComp (originalUpperAffineInv (h0Coordinates g))) haar0 = haar0
  rw [inverse0_coordinates]
  exact haar0_left_invariant (inverse0 g)

/-- A finite relative-coordinate cover yields the source Haar bound; no
measurability of the individual connected components is needed. -/
theorem haar0_finite_relative_box_cover
    {ι : Type*} [Fintype ι] (E : Set Upper) (centers : ι → Quad) (R : ℝ)
    (hcover : ∀ x ∈ E, ∃ i,
      ‖originalUpperRelativeFrame (h0Coordinates (centers i)) x‖ ≤ R) :
    haar0 E ≤ (Fintype.card ι : ℝ≥0∞)*ENNReal.ofReal (2*R)^4 := by
  let T : ι → Set Upper := fun i =>
    originalUpperRelativeFrame (h0Coordinates (centers i)) ⁻¹' upperBox R
  have hsubset : E ⊆ ⋃ i, T i := by
    intro x hx
    obtain ⟨i,hi⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨i,hi⟩
  have hmass (i : ι) : haar0 (T i) = ENNReal.ofReal (2*R)^4 := by
    dsimp only [T]
    have hf : Measurable (originalUpperRelativeFrame (h0Coordinates (centers i))) :=
      measurable_comp_left _
    have hm := congrArg (fun m : Measure Upper => m (upperBox R))
      (haar0_relative_invariant (centers i))
    dsimp only at hm
    rw [Measure.map_apply hf (measurableSet_upperBox R)] at hm
    exact hm.trans (haar0_upperBox R)
  calc
    haar0 E ≤ haar0 (⋃ i, T i) := measure_mono hsubset
    _ ≤ ∑' i, haar0 (T i) := measure_iUnion_le T
    _ = (Fintype.card ι : ℝ≥0∞)*ENNReal.ofReal (2*R)^4 := by simp [hmass]

end PaperI.OriginalHaarWindowBoxes
