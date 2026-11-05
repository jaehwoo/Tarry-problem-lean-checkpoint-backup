import PaperILean.OriginalHaarWindowBoxes
import PaperILean.OriginalHaarWindowSubgroups
import PaperILean.HaarCosetMeasure

/-! The source coordinate Haar normalization for all three specified
subgroups, and its finite-relative-box volume implication. -/
noncomputable section
namespace PaperI.OriginalHaarWindowMeasures
open Set MeasureTheory
open I2385ProductHaar OriginalHaarWindowBoxes
open scoped ENNReal
abbrev Upper := Fin 6 → ℝ

def haarH : Measure Upper := Measure.map HaarCosetMeasure.embed volume

def subgroupHaar : OriginalHaarSubgroup → Measure Upper
  | .H0 => haar0
  | .H3 => haar3
  | .H => haarH

theorem h3_add (u v : Triple) :
    originalUpperAffineComp (h3Coordinates u) (h3Coordinates v) = h3Coordinates (u+v) := by
  ext i
  fin_cases i <;> simp [originalUpperAffineComp,h3Coordinates]

theorem haar3_left_invariant (u : Triple) :
    Measure.map (originalUpperAffineComp (h3Coordinates u)) haar3 = haar3 := by
  unfold haar3
  rw [Measure.map_map (measurable_comp_left _) continuous_h3Coordinates.measurable]
  have heq : originalUpperAffineComp (h3Coordinates u) ∘ h3Coordinates =
      h3Coordinates ∘ (fun v : Triple => u+v) := by funext v; exact h3_add u v
  rw [heq,← Measure.map_map continuous_h3Coordinates.measurable
    (measurePreserving_triple_add_left u).measurable,
    (measurePreserving_triple_add_left u).map_eq]

theorem haarH_left_invariant (u : HaarCosetMeasure.Coordinates) :
    Measure.map (originalUpperAffineComp (HaarCosetMeasure.embed u)) haarH = haarH := by
  unfold haarH
  rw [Measure.map_map (measurable_comp_left _) HaarCosetMeasure.continuous_embed.measurable]
  have heq : originalUpperAffineComp (HaarCosetMeasure.embed u) ∘ HaarCosetMeasure.embed =
      HaarCosetMeasure.embed ∘ (fun v => u+v) := by
    funext v
    exact HaarCosetMeasure.embed_add u v
  rw [heq,← Measure.map_map HaarCosetMeasure.continuous_embed.measurable
    (measurePreserving_add_left (volume : Measure HaarCosetMeasure.Coordinates) u).measurable,
    (measurePreserving_add_left (volume : Measure HaarCosetMeasure.Coordinates) u).map_eq]

theorem haarH_upperBox (R : ℝ) : haarH (upperBox R) = ENNReal.ofReal (2*R)^4 := by
  rw [haarH,Measure.map_apply HaarCosetMeasure.continuous_embed.measurable (measurableSet_upperBox R)]
  have heq : HaarCosetMeasure.embed ⁻¹' upperBox R =
      Icc (fun _ : Fin 4 => -R) (fun _ => R) := by
    ext p
    constructor
    · intro hp
      constructor <;> intro i
      · have h := (norm_le_pi_norm (HaarCosetMeasure.embed p) (i.val+1 : Fin 6)).trans hp
        fin_cases i <;> simp [HaarCosetMeasure.embed] at h ⊢ <;> exact (abs_le.mp h).1
      · have h := (norm_le_pi_norm (HaarCosetMeasure.embed p) (i.val+1 : Fin 6)).trans hp
        fin_cases i <;> simp [HaarCosetMeasure.embed] at h ⊢ <;> exact (abs_le.mp h).2
    · intro hp
      have hR : 0 ≤ R := by
        have h0 : -R ≤ p 0 := hp.1 0
        have h1 : p 0 ≤ R := hp.2 0
        linarith
      apply (pi_norm_le_iff_of_nonneg hR).mpr
      intro i
      fin_cases i <;> simp [HaarCosetMeasure.embed]
      · exact hR
      · exact abs_le.mpr ⟨hp.1 0,hp.2 0⟩
      · exact abs_le.mpr ⟨hp.1 1,hp.2 1⟩
      · exact abs_le.mpr ⟨hp.1 2,hp.2 2⟩
      · exact abs_le.mpr ⟨hp.1 3,hp.2 3⟩
      · exact hR
  rw [heq,Real.volume_Icc_pi]
  simp only [sub_neg_eq_add,← two_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem subgroup_inv_mem (K : OriginalHaarSubgroup) (g : Upper)
    (hg : g ∈ originalHaarSubgroupSet K) :
    originalUpperAffineInv g ∈ originalHaarSubgroupSet K := by
  cases K <;> simp_all [originalHaarSubgroupSet,originalUpperAffineInv]

theorem subgroup_left_invariant (K : OriginalHaarSubgroup) (g : Upper)
    (hg : g ∈ originalHaarSubgroupSet K) :
    Measure.map (originalUpperAffineComp g) (subgroupHaar K) = subgroupHaar K := by
  cases K
  · have h := haar0_left_invariant (g 3,(g 0,g 1,g 2))
    rw [h0Coordinates_parametrize hg] at h
    exact h
  · have h := haar3_left_invariant (g 0,g 1,g 2)
    rw [h3Coordinates_parametrize hg] at h
    exact h
  · have he : HaarCosetMeasure.embed ![g 1,g 2,g 3,g 4] = g := by
      ext i
      fin_cases i <;> simp_all [HaarCosetMeasure.embed,originalHaarSubgroupSet]
    have h := haarH_left_invariant ![g 1,g 2,g 3,g 4]
    rw [he] at h
    exact h

theorem subgroup_relative_invariant (K : OriginalHaarSubgroup) (g : Upper)
    (hg : g ∈ originalHaarSubgroupSet K) :
    Measure.map (originalUpperRelativeFrame g) (subgroupHaar K) = subgroupHaar K := by
  change Measure.map (originalUpperAffineComp (originalUpperAffineInv g)) (subgroupHaar K) = _
  exact subgroup_left_invariant K _ (subgroup_inv_mem K g hg)

/-- A common fourth-power bound works for all three source subgroups when
R>=1; the H3 coordinate mass is exactly the third power. -/
theorem subgroup_upperBox_bound (K : OriginalHaarSubgroup) (R : ℝ) (hR : 1 ≤ R) :
    subgroupHaar K (upperBox R) ≤ ENNReal.ofReal (2*R)^4 := by
  cases K
  · exact le_of_eq (haar0_upperBox R)
  · change haar3 (upperBox R) ≤ _
    rw [haar3_upperBox]
    have hbase : (1:ℝ≥0∞) ≤ ENNReal.ofReal (2*R) := by
      exact (ENNReal.one_le_ofReal).mpr (by linarith)
    exact pow_le_pow_right₀ hbase (by omega : 3 ≤ 4)
  · exact le_of_eq (haarH_upperBox R)

/-- Finite component-relative boxes give Haar volume under the source
normalization, without assuming individual components measurable. -/
theorem finite_relative_box_cover
    {ι : Type*} [Fintype ι] (K : OriginalHaarSubgroup) (E : Set Upper)
    (centers : ι → Upper) (R : ℝ) (hR : 1 ≤ R)
    (hcenters : ∀ i, centers i ∈ originalHaarSubgroupSet K)
    (hcover : ∀ x ∈ E, ∃ i, ‖originalUpperRelativeFrame (centers i) x‖ ≤ R) :
    subgroupHaar K E ≤ (Fintype.card ι : ℝ≥0∞)*ENNReal.ofReal (2*R)^4 := by
  let T : ι → Set Upper := fun i => originalUpperRelativeFrame (centers i) ⁻¹' upperBox R
  have hsub : E ⊆ ⋃ i, T i := by
    intro x hx
    obtain ⟨i,hi⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨i,hi⟩
  have hmass (i : ι) : subgroupHaar K (T i) ≤ ENNReal.ofReal (2*R)^4 := by
    have hf : Measurable (originalUpperRelativeFrame (centers i)) := measurable_comp_left _
    have he := congrArg (fun m : Measure Upper => m (upperBox R))
      (subgroup_relative_invariant K (centers i) (hcenters i))
    dsimp only at he
    rw [Measure.map_apply hf (measurableSet_upperBox R)] at he
    exact he.trans_le (subgroup_upperBox_bound K R hR)
  calc
    subgroupHaar K E ≤ subgroupHaar K (⋃ i, T i) := measure_mono hsub
    _ ≤ ∑' i, subgroupHaar K (T i) := measure_iUnion_le T
    _ ≤ ∑' _i : ι, ENNReal.ofReal (2*R)^4 := ENNReal.tsum_le_tsum hmass
    _ = (Fintype.card ι : ℝ≥0∞)*ENNReal.ofReal (2*R)^4 := by simp

end PaperI.OriginalHaarWindowMeasures
