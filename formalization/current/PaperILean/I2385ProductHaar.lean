import PaperILean.OriginalGaussFixedFrameArea
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic

/-! I2385, with the coordinate Lebesgue normalization from I2339.
The maps below use the actual original six-coordinate affine composition.
No null-density, pivot, conditional volume or main-theorem premise is used. -/

noncomputable section
namespace PaperI.I2385ProductHaar

open Set MeasureTheory
open scoped ENNReal

abbrev Upper := Fin 6 → ℝ
abbrev Triple := ℝ × (ℝ × ℝ)
abbrev Quad := ℝ × Triple

/-- The four ordinary coordinates, ordered `(d,a,b,c₀)` for Tonelli. -/
def h0Coordinates (p : Quad) : Upper :=
  ![p.2.1, p.2.2.1, p.2.2.2, p.1, 0, 0]

def h3Coordinates (u : Triple) : Upper :=
  ![u.1, u.2.1, u.2.2, 0, 0, 0]

def shear (t : ℝ) : Upper := ![0, 0, 0, t, 0, 0]

def H0 (g : Upper) : Prop := g 4 = 0 ∧ g 5 = 0
def H3 (g : Upper) : Prop := g 3 = 0 ∧ g 4 = 0 ∧ g 5 = 0

theorem h0Coordinates_mem (p : Quad) : H0 (h0Coordinates p) := by
  simp [H0, h0Coordinates]

theorem h3Coordinates_mem (u : Triple) : H3 (h3Coordinates u) := by
  simp [H3, h3Coordinates]

theorem h0Coordinates_parametrize {g : Upper} (hg : H0 g) :
    h0Coordinates (g 3, (g 0, g 1, g 2)) = g := by
  ext i
  fin_cases i <;> simp [h0Coordinates, H0, hg.1, hg.2]

theorem h3Coordinates_parametrize {g : Upper} (hg : H3 g) :
    h3Coordinates (g 0, g 1, g 2) = g := by
  ext i
  fin_cases i <;> simp [h3Coordinates, H3, hg.1, hg.2.1, hg.2.2]

theorem continuous_h0Coordinates : Continuous h0Coordinates := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [h0Coordinates] <;> fun_prop

theorem continuous_h3Coordinates : Continuous h3Coordinates := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [h3Coordinates] <;> fun_prop

theorem measurableEmbedding_h3Coordinates : MeasurableEmbedding h3Coordinates := by
  apply continuous_h3Coordinates.measurableEmbedding
  intro u v huv
  apply Prod.ext
  · simpa [h3Coordinates] using congrFun huv 0
  · apply Prod.ext
    · simpa [h3Coordinates] using congrFun huv 1
    · simpa [h3Coordinates] using congrFun huv 2

theorem continuous_shear : Continuous shear := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [shear] <;> fun_prop

theorem measurable_comp_left (g : Upper) :
    Measurable (originalUpperAffineComp g) := by
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i <;> simp [originalUpperAffineComp] <;> fun_prop

theorem measurable_comp_right (g : Upper) :
    Measurable (fun h => originalUpperAffineComp h g) := by
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i <;> simp [originalUpperAffineComp] <;> fun_prop

/-- Coordinate Lebesgue measure on the actual subgroup, represented in `Upper`. -/
def haar0 : Measure Upper := Measure.map h0Coordinates volume
def haar3 : Measure Upper := Measure.map h3Coordinates volume

/-- The actual opposite-order change on the three-dimensional fiber. -/
def fiberShear (t : ℝ) (u : Triple) : Triple :=
  (u.1, (u.2.1 + u.1 * t, u.2.2))

theorem measurePreserving_fiberShear (t : ℝ) :
    MeasurePreserving (fiberShear t) volume volume := by
  have hpair (a : ℝ) :
      MeasurePreserving (fun q : ℝ × ℝ => (q.1 + a * t, q.2)) volume volume := by
    exact (measurePreserving_add_right (volume : Measure ℝ) (a * t)).prod
      (MeasurePreserving.id (volume : Measure ℝ))
  simpa only [fiberShear] using
    (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun a (q : ℝ × ℝ) => (q.1 + a * t, q.2))
      (by fun_prop)
      (Filter.Eventually.of_forall fun a => (hpair a).map_eq)

def productShear (p : Quad) : Quad := (p.1, fiberShear p.1 p.2)

theorem measurePreserving_productShear :
    MeasurePreserving productShear volume volume := by
  simpa only [productShear] using
    (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fiberShear)
      (by unfold fiberShear; fun_prop)
      (Filter.Eventually.of_forall fun t => (measurePreserving_fiberShear t).map_eq)

def coordinateLeft (g p : Quad) : Quad :=
  (g.1 + p.1, (g.2.1, (g.2.2.1 + g.2.1 * p.1, g.2.2.2)) + p.2)

def coordinateRight (g p : Quad) : Quad :=
  (p.1 + g.1, fiberShear g.1 p.2 + g.2)

theorem measurePreserving_triple_add_left (v : Triple) :
    MeasurePreserving (fun u : Triple => v + u) volume volume := by
  exact (measurePreserving_add_left (volume : Measure ℝ) v.1).prod
    ((measurePreserving_add_left (volume : Measure ℝ) v.2.1).prod
      (measurePreserving_add_left (volume : Measure ℝ) v.2.2))

theorem measurePreserving_triple_add_right (v : Triple) :
    MeasurePreserving (fun u : Triple => u + v) volume volume := by
  exact (measurePreserving_add_right (volume : Measure ℝ) v.1).prod
    ((measurePreserving_add_right (volume : Measure ℝ) v.2.1).prod
      (measurePreserving_add_right (volume : Measure ℝ) v.2.2))

theorem measurePreserving_coordinateLeft (g : Quad) :
    MeasurePreserving (coordinateLeft g) volume volume := by
  simpa only [coordinateLeft] using
    (measurePreserving_add_left (volume : Measure ℝ) g.1).skew_product
      (g := fun t (u : Triple) =>
        (g.2.1, (g.2.2.1 + g.2.1 * t, g.2.2.2)) + u)
      (by fun_prop)
      (Filter.Eventually.of_forall fun t =>
        (measurePreserving_triple_add_left
          (g.2.1, (g.2.2.1 + g.2.1 * t, g.2.2.2))).map_eq)

theorem measurePreserving_coordinateRight (g : Quad) :
    MeasurePreserving (coordinateRight g) volume volume := by
  simpa only [coordinateRight, Function.comp_def, Prod.map_apply] using
    (measurePreserving_add_right (volume : Measure ℝ) g.1).prod
      ((measurePreserving_triple_add_right g.2).comp
        (measurePreserving_fiberShear g.1))

theorem actual_left_translation (g p : Quad) :
    originalUpperAffineComp (h0Coordinates g) (h0Coordinates p) =
      h0Coordinates (coordinateLeft g p) := by
  ext i
  fin_cases i <;> simp [originalUpperAffineComp, h0Coordinates, coordinateLeft] <;> ring

theorem actual_right_translation (g p : Quad) :
    originalUpperAffineComp (h0Coordinates p) (h0Coordinates g) =
      h0Coordinates (coordinateRight g p) := by
  ext i
  fin_cases i <;> simp [originalUpperAffineComp, h0Coordinates, coordinateRight, fiberShear] <;> ring

theorem haar0_left_invariant (g : Quad) :
    Measure.map (originalUpperAffineComp (h0Coordinates g)) haar0 = haar0 := by
  unfold haar0
  rw [Measure.map_map (measurable_comp_left _) continuous_h0Coordinates.measurable]
  have heq : originalUpperAffineComp (h0Coordinates g) ∘ h0Coordinates =
      h0Coordinates ∘ coordinateLeft g := by
    funext p
    exact actual_left_translation g p
  rw [heq, ← Measure.map_map continuous_h0Coordinates.measurable
    (measurePreserving_coordinateLeft g).measurable,
    (measurePreserving_coordinateLeft g).map_eq]

theorem haar0_right_invariant (g : Quad) :
    Measure.map (fun h => originalUpperAffineComp h (h0Coordinates g)) haar0 = haar0 := by
  unfold haar0
  rw [Measure.map_map (measurable_comp_right _) continuous_h0Coordinates.measurable]
  have heq : (fun h => originalUpperAffineComp h (h0Coordinates g)) ∘ h0Coordinates =
      h0Coordinates ∘ coordinateRight g := by
    funext p
    exact actual_right_translation g p
  rw [heq, ← Measure.map_map continuous_h0Coordinates.measurable
    (measurePreserving_coordinateRight g).measurable,
    (measurePreserving_coordinateRight g).map_eq]

def leftProduct (p : Quad) : Upper :=
  originalUpperAffineComp (shear p.1) (h3Coordinates p.2)

def rightProduct (p : Quad) : Upper :=
  originalUpperAffineComp (h3Coordinates p.2) (shear p.1)

theorem leftProduct_eq (p : Quad) : leftProduct p = h0Coordinates p := by
  ext i
  fin_cases i <;> simp [leftProduct, shear, h3Coordinates, h0Coordinates,
    originalUpperAffineComp]

theorem rightProduct_eq (p : Quad) :
    rightProduct p = h0Coordinates (productShear p) := by
  ext i
  fin_cases i <;> simp [rightProduct, shear, h3Coordinates, h0Coordinates,
    originalUpperAffineComp, productShear, fiberShear]

theorem measurePreserving_leftProduct :
    MeasurePreserving leftProduct volume haar0 := by
  have heq : leftProduct = h0Coordinates := funext leftProduct_eq
  rw [heq]
  exact ⟨continuous_h0Coordinates.measurable, rfl⟩

theorem measurePreserving_rightProduct :
    MeasurePreserving rightProduct volume haar0 := by
  have heq : rightProduct = h0Coordinates ∘ productShear := funext rightProduct_eq
  rw [heq]
  exact (show MeasurePreserving h0Coordinates volume haar0 from
    ⟨continuous_h0Coordinates.measurable, rfl⟩).comp measurePreserving_productShear

/-- The exact normalized product-measure equality, for both actual orientations. -/
theorem product_haar_measure :
    Measure.map leftProduct ((volume : Measure ℝ).prod (volume : Measure Triple)) = haar0 ∧
    Measure.map rightProduct ((volume : Measure ℝ).prod (volume : Measure Triple)) = haar0 := by
  exact ⟨measurePreserving_leftProduct.map_eq, measurePreserving_rightProduct.map_eq⟩

/-- Tonelli form of the complete display I2385, with no integrability assumption. -/
theorem product_haar_lintegral (F : Upper → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ k, F k ∂haar0) =
      ∫⁻ t : ℝ, ∫⁻ u : Triple,
        F (originalUpperAffineComp (shear t) (h3Coordinates u)) ∧
    (∫⁻ k, F k ∂haar0) =
      ∫⁻ t : ℝ, ∫⁻ u : Triple,
        F (originalUpperAffineComp (h3Coordinates u) (shear t)) := by
  constructor
  · rw [← measurePreserving_leftProduct.lintegral_comp hF]
    exact lintegral_prod _ (hF.comp measurePreserving_leftProduct.measurable).aemeasurable
  · rw [← measurePreserving_rightProduct.lintegral_comp hF]
    exact lintegral_prod _ (hF.comp measurePreserving_rightProduct.measurable).aemeasurable

def shearWindow (I : Set ℝ) : Set Upper := {g | g 3 ∈ I}

theorem measurableSet_shearWindow {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurableSet (shearWindow I) :=
  hI.preimage (measurable_pi_apply 3)

theorem leftProduct_preimage_shearWindow (I : Set ℝ) :
    leftProduct ⁻¹' shearWindow I = I ×ˢ (Set.univ : Set Triple) := by
  ext p
  simp [shearWindow, leftProduct_eq, h0Coordinates]

theorem rightProduct_preimage_shearWindow (I : Set ℝ) :
    rightProduct ⁻¹' shearWindow I = I ×ˢ (Set.univ : Set Triple) := by
  ext p
  simp [shearWindow, rightProduct_eq, h0Coordinates, productShear]

theorem measurePreserving_leftProduct_restrict {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurePreserving leftProduct
      (((volume : Measure ℝ).restrict I).prod (volume : Measure Triple))
      (haar0.restrict (shearWindow I)) := by
  have h := measurePreserving_leftProduct.restrict_preimage (measurableSet_shearWindow hI)
  rw [leftProduct_preimage_shearWindow] at h
  change MeasurePreserving leftProduct
    (((volume : Measure ℝ).prod (volume : Measure Triple)).restrict (I ×ˢ Set.univ)) _ at h
  rw [← Measure.restrict_prod_eq_prod_univ] at h
  exact h

theorem measurePreserving_rightProduct_restrict {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurePreserving rightProduct
      (((volume : Measure ℝ).restrict I).prod (volume : Measure Triple))
      (haar0.restrict (shearWindow I)) := by
  have h := measurePreserving_rightProduct.restrict_preimage (measurableSet_shearWindow hI)
  rw [rightProduct_preimage_shearWindow] at h
  change MeasurePreserving rightProduct
    (((volume : Measure ℝ).prod (volume : Measure Triple)).restrict (I ×ˢ Set.univ)) _ at h
  rw [← Measure.restrict_prod_eq_prod_univ] at h
  exact h

/-- The entire product disintegration, with any Borel shear window. -/
theorem restricted_product_haar_measure {I : Set ℝ} (hI : MeasurableSet I) :
    Measure.map leftProduct
        (((volume : Measure ℝ).restrict I).prod (volume : Measure Triple)) =
      haar0.restrict (shearWindow I) ∧
    Measure.map rightProduct
        (((volume : Measure ℝ).restrict I).prod (volume : Measure Triple)) =
      haar0.restrict (shearWindow I) :=
  ⟨(measurePreserving_leftProduct_restrict hI).map_eq,
    (measurePreserving_rightProduct_restrict hI).map_eq⟩

theorem restricted_product_haar_lintegral {I : Set ℝ} (hI : MeasurableSet I)
    (F : Upper → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ k in shearWindow I, F k ∂haar0) =
      ∫⁻ t : ℝ in I, ∫⁻ u : Triple,
        F (originalUpperAffineComp (shear t) (h3Coordinates u)) ∧
    (∫⁻ k in shearWindow I, F k ∂haar0) =
      ∫⁻ t : ℝ in I, ∫⁻ u : Triple,
        F (originalUpperAffineComp (h3Coordinates u) (shear t)) := by
  constructor
  · rw [← (measurePreserving_leftProduct_restrict hI).lintegral_comp hF]
    exact lintegral_prod _
      (hF.comp (measurePreserving_leftProduct_restrict hI).measurable).aemeasurable
  · rw [← (measurePreserving_rightProduct_restrict hI).lintegral_comp hF]
    exact lintegral_prod _
      (hF.comp (measurePreserving_rightProduct_restrict hI).measurable).aemeasurable

theorem haar3_lintegral_left (t : ℝ) (F : Upper → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, F (originalUpperAffineComp (shear t) s) ∂haar3) =
      ∫⁻ u : Triple, F (originalUpperAffineComp (shear t) (h3Coordinates u)) := by
  exact lintegral_map (hF.comp (measurable_comp_left _)) continuous_h3Coordinates.measurable

theorem haar3_lintegral_right (t : ℝ) (F : Upper → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, F (originalUpperAffineComp s (shear t)) ∂haar3) =
      ∫⁻ u : Triple, F (originalUpperAffineComp (h3Coordinates u) (shear t)) := by
  exact lintegral_map (hF.comp (measurable_comp_right _)) continuous_h3Coordinates.measurable

/-- The manuscript's literal Haar measures occur in both inner and outer integrals. -/
theorem product_haar_stage (F : Upper → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ k, F k ∂haar0) =
      ∫⁻ t : ℝ, ∫⁻ s, F (originalUpperAffineComp (shear t) s) ∂haar3 ∧
    (∫⁻ k, F k ∂haar0) =
      ∫⁻ t : ℝ, ∫⁻ s, F (originalUpperAffineComp s (shear t)) ∂haar3 := by
  constructor
  · rw [(product_haar_lintegral F hF).1]
    exact lintegral_congr_ae (Filter.Eventually.of_forall fun t =>
      (haar3_lintegral_left t F hF).symm)
  · rw [(product_haar_lintegral F hF).2]
    exact lintegral_congr_ae (Filter.Eventually.of_forall fun t =>
      (haar3_lintegral_right t F hF).symm)

theorem restricted_product_haar_stage {I : Set ℝ} (hI : MeasurableSet I)
    (F : Upper → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ k in shearWindow I, F k ∂haar0) =
      ∫⁻ t : ℝ in I, ∫⁻ s, F (originalUpperAffineComp (shear t) s) ∂haar3 ∧
    (∫⁻ k in shearWindow I, F k ∂haar0) =
      ∫⁻ t : ℝ in I, ∫⁻ s, F (originalUpperAffineComp s (shear t)) ∂haar3 := by
  constructor
  · rw [(restricted_product_haar_lintegral hI F hF).1]
    exact lintegral_congr_ae (Filter.Eventually.of_forall fun t =>
      (haar3_lintegral_left t F hF).symm)
  · rw [(restricted_product_haar_lintegral hI F hF).2]
    exact lintegral_congr_ae (Filter.Eventually.of_forall fun t =>
      (haar3_lintegral_right t F hF).symm)

private theorem integral_of_measurePreserving {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν)
    (F : β → E) (hF : Integrable F ν) :
    (∫ y, F y ∂ν) = ∫ x, F (f x) ∂μ := by
  have hm : AEStronglyMeasurable F (Measure.map f μ) := by
    rw [hf.map_eq]
    exact hF.aestronglyMeasurable
  rw [← integral_map hf.measurable.aemeasurable hm, hf.map_eq]

/-- Fubini for integrable real, complex, or normed real-vector-valued functions. -/
theorem restricted_product_haar_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {I : Set ℝ} (hI : MeasurableSet I) (F : Upper → E)
    (hF : Integrable F (haar0.restrict (shearWindow I))) :
    (∫ k in shearWindow I, F k ∂haar0) =
      ∫ t : ℝ in I, ∫ u : Triple,
        F (originalUpperAffineComp (shear t) (h3Coordinates u)) ∧
    (∫ k in shearWindow I, F k ∂haar0) =
      ∫ t : ℝ in I, ∫ u : Triple,
        F (originalUpperAffineComp (h3Coordinates u) (shear t)) := by
  have hl := measurePreserving_leftProduct_restrict hI
  have hr := measurePreserving_rightProduct_restrict hI
  have hfl := (hl.integrable_comp hF.aestronglyMeasurable).mpr hF
  have hfr := (hr.integrable_comp hF.aestronglyMeasurable).mpr hF
  constructor
  · rw [integral_of_measurePreserving hl F hF]
    exact integral_prod _ hfl
  · rw [integral_of_measurePreserving hr F hF]
    exact integral_prod _ hfr

theorem haar3_integral_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℝ) (F : Upper → E) :
    (∫ s, F (originalUpperAffineComp (shear t) s) ∂haar3) =
      ∫ u : Triple, F (originalUpperAffineComp (shear t) (h3Coordinates u)) :=
  measurableEmbedding_h3Coordinates.integral_map _

theorem haar3_integral_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℝ) (F : Upper → E) :
    (∫ s, F (originalUpperAffineComp s (shear t)) ∂haar3) =
      ∫ u : Triple, F (originalUpperAffineComp (h3Coordinates u) (shear t)) :=
  measurableEmbedding_h3Coordinates.integral_map _

theorem restricted_product_haar_integral_stage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {I : Set ℝ} (hI : MeasurableSet I) (F : Upper → E)
    (hF : Integrable F (haar0.restrict (shearWindow I))) :
    (∫ k in shearWindow I, F k ∂haar0) =
      ∫ t : ℝ in I, ∫ s, F (originalUpperAffineComp (shear t) s) ∂haar3 ∧
    (∫ k in shearWindow I, F k ∂haar0) =
      ∫ t : ℝ in I, ∫ s, F (originalUpperAffineComp s (shear t)) ∂haar3 := by
  constructor
  · rw [(restricted_product_haar_integral hI F hF).1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
      (haar3_integral_left t F).symm)
  · rw [(restricted_product_haar_integral hI F hF).2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
      (haar3_integral_right t F).symm)

theorem product_haar_integral_stage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : Upper → E) (hF : Integrable F haar0) :
    (∫ k, F k ∂haar0) =
      ∫ t : ℝ, ∫ s, F (originalUpperAffineComp (shear t) s) ∂haar3 ∧
    (∫ k, F k ∂haar0) =
      ∫ t : ℝ, ∫ s, F (originalUpperAffineComp s (shear t)) ∂haar3 := by
  have hs : shearWindow Set.univ = Set.univ := by ext g; simp [shearWindow]
  have h := restricted_product_haar_integral_stage MeasurableSet.univ F
    (by simpa only [hs, Measure.restrict_univ] using hF)
  simpa only [hs, Measure.restrict_univ] using h

end PaperI.I2385ProductHaar
