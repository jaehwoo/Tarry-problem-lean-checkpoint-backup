import PaperILean.FreeSliceRows
import PaperILean.IndexCombinatorics
import PaperILean.UpperAffineCoefficientDetOne
import Mathlib.MeasureTheory.Measure.Map

/-! I3353[269,409): the four actual normalization rows leave exactly the
complementary coefficient coordinates free. The measure below is intrinsic
product Lebesgue in those coordinates, not ambient measure restricted to a
lower-dimensional slice. Regular endpoints satisfy further restrictions;
arbitrary free coefficients are not asserted to remain regular. -/

noncomputable section
namespace PaperI.FreeSliceCoordinates

open MeasureTheory Filter FreeSliceRows
open scoped Topology

/-- The ordinary monomial indices excluding exactly the four normal rows. -/
def FreeIndex {k : ℕ} (hk : 3 ≤ k) :=
  {a : MonomialIndex k // a ∉ Set.range (normalIndex hk)}

instance {k : ℕ} (hk : 3 ≤ k) : Fintype (FreeIndex hk) := by
  classical
  unfold FreeIndex
  infer_instance

/-- The full linear normalization slice, before regularity or window restrictions. -/
noncomputable def normalSlice {k : ℕ} (hk : 3 ≤ k) : Submodule ℝ (CoefficientSpace k) where
  carrier := {J | ∀ i, J (normalIndex hk i) = 0}
  zero_mem' := by intro i; rfl
  add_mem' := by intro J K hJ hK i; simp [hJ i, hK i]
  smul_mem' := by intro a J hJ i; simp [hJ i]

/-- Literal extension of the remaining coordinates, with zero normal rows. -/
def zeroExtension {k : ℕ} (hk : 3 ≤ k) (v : FreeIndex hk → ℝ) :
    CoefficientSpace k := by
  classical
  exact fun a => if ha : a ∈ Set.range (normalIndex hk) then 0 else v ⟨a, ha⟩

@[simp] theorem zeroExtension_normal {k : ℕ} (hk : 3 ≤ k)
    (v : FreeIndex hk → ℝ) (i : Fin 4) :
    zeroExtension hk v (normalIndex hk i) = 0 := by
  classical
  simp [zeroExtension]

@[simp] theorem zeroExtension_free {k : ℕ} (hk : 3 ≤ k)
    (v : FreeIndex hk → ℝ) (a : FreeIndex hk) :
    zeroExtension hk v a.val = v a := by
  classical
  simp [zeroExtension, a.property]

/-- Restriction and zero extension are mutually inverse on the actual coefficient slice. -/
def freeSliceEquiv {k : ℕ} (hk : 3 ≤ k) :
    normalSlice hk ≃ₗ[ℝ] (FreeIndex hk → ℝ) where
  toFun J a := J.val a.val
  invFun v := ⟨zeroExtension hk v, zeroExtension_normal hk v⟩
  left_inv J := by
    apply Subtype.ext
    funext a
    change zeroExtension hk (fun b : FreeIndex hk => J.val b.val) a = J.val a
    by_cases ha : a ∈ Set.range (normalIndex hk)
    · obtain ⟨i, rfl⟩ := ha
      exact (zeroExtension_normal hk (fun b => J.val b.val) i).trans (J.property i).symm
    · exact zeroExtension_free hk (fun b => J.val b.val) ⟨a, ha⟩
  right_inv v := by
    funext a
    exact zeroExtension_free hk v a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem freeSliceEquiv_apply {k : ℕ} (hk : 3 ≤ k)
    (J : normalSlice hk) (a : FreeIndex hk) :
    freeSliceEquiv hk J a = J.val a.val := rfl

@[simp] theorem freeSliceEquiv_symm_apply {k : ℕ} (hk : 3 ≤ k)
    (v : FreeIndex hk → ℝ) :
    ((freeSliceEquiv hk).symm v).val = zeroExtension hk v := rfl

theorem slice_reconstruction {k : ℕ} (hk : 3 ≤ k) (J : normalSlice hk) :
    zeroExtension hk (fun a : FreeIndex hk => J.val a.val) = J.val :=
  congrArg Subtype.val ((freeSliceEquiv hk).symm_apply_apply J)

theorem mem_normalSlice_iff_rawRows {k : ℕ} (hk : 3 ≤ k) (J : CoefficientSpace k) :
    J ∈ normalSlice hk ↔ rawRows (coefficientPolynomial J) = 0 := by
  change (∀ i, J (normalIndex hk i) = 0) ↔ _
  constructor
  · intro h
    funext i
    exact (rawRows_coefficient J hk i).trans (h i)
  · intro h i
    rw [← rawRows_coefficient J hk]
    exact congrFun h i

theorem card_freeIndex {k : ℕ} (hk : 3 ≤ k) :
    Fintype.card (FreeIndex hk) = dimension k - 4 := by
  classical
  have hrange : Fintype.card (Set.range (normalIndex hk)) = 4 := by
    rw [← Fintype.card_congr (Equiv.ofInjective (normalIndex hk)
      (normalIndex_injective hk))]
    exact Fintype.card_fin 4
  change Fintype.card {a : MonomialIndex k // a ∉ Set.range (normalIndex hk)} = _
  rw [Fintype.card_subtype_compl, hrange, card_monomialIndex]

/-- Product Lebesgue in the literal free monomial coordinates. -/
def freeCoefficientMeasure {k : ℕ} (hk : 3 ≤ k) : Measure (FreeIndex hk → ℝ) :=
  Measure.pi fun _ => (volume : Measure ℝ)

def freeSliceMeasurableEquiv {k : ℕ} (hk : 3 ≤ k) :
    normalSlice hk ≃ᵐ (FreeIndex hk → ℝ) where
  toEquiv := (freeSliceEquiv hk).toEquiv
  measurable_toFun := measurable_pi_lambda _ fun a =>
    (measurable_pi_apply a.val).comp measurable_subtype_coe
  measurable_invFun := by
    change Measurable (fun v => (⟨zeroExtension hk v, zeroExtension_normal hk v⟩ : normalSlice hk))
    apply Measurable.subtype_mk
    apply measurable_pi_lambda
    intro a
    classical
    by_cases ha : a ∈ Set.range (normalIndex hk)
    · simp only [zeroExtension, dif_pos ha]
      exact measurable_const
    · simp only [zeroExtension, dif_neg ha]
      exact measurable_pi_apply (⟨a, ha⟩ : FreeIndex hk)

/-- The manuscript's intrinsic dJ measure on the linear normalization slice. -/
def intrinsicSliceMeasure {k : ℕ} (hk : 3 ≤ k) : Measure (normalSlice hk) :=
  Measure.map (freeSliceMeasurableEquiv hk).symm (freeCoefficientMeasure hk)

theorem slice_coordinates_measure {k : ℕ} (hk : 3 ≤ k) :
    Measure.map (freeSliceEquiv hk) (intrinsicSliceMeasure hk) =
      Measure.pi (fun _ : FreeIndex hk => (volume : Measure ℝ)) := by
  exact MeasurableEquiv.map_map_symm (freeSliceMeasurableEquiv hk)

/-- I3353[269,409): the complete free-coordinate stage at an ordinary regular
normalized endpoint. The degree guard is derived from the same graph. The
determinant-one conclusion concerns the full coefficient map, not its
restriction to the slice. The joint incidence formula is a separate obligation. -/
theorem free_coefficient_slice_stage {k : ℕ} (J : CoefficientSpace k)
    (c : (Fin 2 → ℝ) → ℝ)
    (hc : ContinuousAt c 0) (hc0 : c 0 = 0) (hDc : fderiv ℝ c 0 = 0)
    (hroot : ∀ᶠ v in 𝓝 0,
      MvPolynomial.eval ![c v, v 0, v 1]
        (MvPolynomial.pderiv 0 (coefficientPolynomial J)) = 0)
    (hrows : rawRows (coefficientPolynomial J) = 0)
    (hlam : MvPolynomial.eval 0
      (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (coefficientPolynomial J))) ≠ 0)
    (hr : PhysicalGaussPivot.graphYY c ≠ 0) :
    ∃ hk : 3 ≤ k,
      J ∈ normalSlice hk ∧
      (∀ Q : CoefficientSpace k,
        rawRows (coefficientPolynomial Q) = 0 ↔ Q ∈ normalSlice hk) ∧
      Function.Bijective (freeSliceEquiv hk) ∧
      (∀ Q : normalSlice hk,
        zeroExtension hk (fun a : FreeIndex hk => Q.val a.val) = Q.val) ∧
      Fintype.card (FreeIndex hk) = dimension k - 4 ∧
      Measure.map (freeSliceEquiv hk) (intrinsicSliceMeasure hk) =
        Measure.pi (fun _ : FreeIndex hk => (volume : Measure ℝ)) ∧
      (∀ g : Fin 6 → ℝ,
        LinearMap.det (affineCoefficientMap k ![g 2, g 4, g 5]
          (originalUpperLinearMatrix g)) = 1) := by
  have hk := degree_ge_three_of_regular_graph J c hc hc0 hDc hroot hlam hr
  exact ⟨hk, (mem_normalSlice_iff_rawRows hk J).mpr hrows,
    fun Q => (mem_normalSlice_iff_rawRows hk Q).symm,
    (freeSliceEquiv hk).bijective, slice_reconstruction hk, card_freeIndex hk,
    slice_coordinates_measure hk, originalUpperAffineCoefficient_det_one k⟩

end PaperI.FreeSliceCoordinates
