import PaperILean.OriginalGaussFixedFrameArea
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-! I2330[153,239): actual left/right H cosets and their transported Haar measures.
The actual upper-affine operation is used on six coordinates throughout.
Only its restriction to H is identified with additive four-space, by proof.
The result allows every fixed additive Haar normalization in that chart. -/

noncomputable section

namespace PaperI.HaarCosetMeasure

open MeasureTheory

abbrev Frame := Fin 6 → ℝ
abbrev Coordinates := Fin 4 → ℝ

/-- The actual coordinate chart of H={a=f=0}, ordered (b,c0,d,e). -/
def embed (u : Coordinates) : Frame := ![0, u 0, u 1, u 2, u 3, 0]

def H : Set Frame := {g | g 0 = 0 ∧ g 5 = 0}

theorem embed_mem (u : Coordinates) : embed u ∈ H := by
  simp [embed, H]

theorem range_embed : Set.range embed = H := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact embed_mem u
  · rintro ⟨ha, hf⟩
    refine ⟨![g 1, g 2, g 3, g 4], ?_⟩
    ext i
    fin_cases i <;> simp [embed, ha, hf]

theorem embed_injective : Function.Injective embed := by
  intro u v h
  ext i
  fin_cases i
  · simpa [embed] using congrFun h 1
  · simpa [embed] using congrFun h 2
  · simpa [embed] using congrFun h 3
  · simpa [embed] using congrFun h 4

/-- This is the actual group law restricted to the chart, not an ambient replacement. -/
theorem embed_add (u v : Coordinates) :
    originalUpperAffineComp (embed u) (embed v) = embed (u + v) := by
  ext i
  fin_cases i <;> simp [originalUpperAffineComp, embed]

theorem continuous_embed : Continuous embed := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [embed] <;> fun_prop

def shearS (a : ℝ) (u : Coordinates) : Coordinates :=
  ![u 0 + a * u 2, u 1 + a * u 3, u 2, u 3]

def shearT (f : ℝ) (u : Coordinates) : Coordinates :=
  ![u 0, u 1 - f * u 0, u 2, u 3 - f * u 2]

def adjoint (a f : ℝ) (u : Coordinates) : Coordinates :=
  ![u 0 + a * u 2, u 1 - f * u 0 + a * u 3 - a * f * u 2,
    u 2, u 3 - f * u 2]

theorem adjoint_eq_shears (a f : ℝ) : adjoint a f = shearS a ∘ shearT f := by
  funext u
  ext i
  fin_cases i <;> simp [adjoint, shearS, shearT, Function.comp_apply] <;> ring

theorem actual_conjugation (g : Frame) (u : Coordinates) :
    originalUpperAffineComp (originalUpperAffineComp g (embed u))
      (originalUpperAffineInv g) = embed (adjoint (g 0) (g 5) u) := by
  ext i
  fin_cases i <;> simp [originalUpperAffineComp, originalUpperAffineInv, embed,
    adjoint] <;> ring

theorem actual_left_eq_right_adjoint (g : Frame) (u : Coordinates) :
    originalUpperAffineComp g (embed u) =
      originalUpperAffineComp (embed (adjoint (g 0) (g 5) u)) g := by
  ext i
  fin_cases i <;> simp [originalUpperAffineComp, embed, adjoint] <;> ring

def shearSLinear (a : ℝ) : Coordinates →ₗ[ℝ] Coordinates where
  toFun := shearS a
  map_add' u v := by
    ext i
    fin_cases i <;> simp [shearS] <;> ring
  map_smul' c u := by
    ext i
    fin_cases i <;> simp [shearS] <;> ring

def shearTLinear (f : ℝ) : Coordinates →ₗ[ℝ] Coordinates where
  toFun := shearT f
  map_add' u v := by
    ext i
    fin_cases i <;> simp [shearT] <;> ring
  map_smul' c u := by
    ext i
    fin_cases i <;> simp [shearT] <;> ring

def adjointLinearEquiv (a f : ℝ) : Coordinates ≃ₗ[ℝ] Coordinates where
  toFun := adjoint a f
  invFun := adjoint (-a) (-f)
  left_inv u := by
    ext i
    fin_cases i <;> simp [adjoint] <;> ring
  right_inv u := by
    ext i
    fin_cases i <;> simp [adjoint] <;> ring
  map_add' u v := by
    ext i
    fin_cases i <;> simp [adjoint] <;> ring
  map_smul' c u := by
    ext i
    fin_cases i <;> simp [adjoint] <;> ring

theorem adjoint_linear_factorization (a f : ℝ) :
    (adjointLinearEquiv a f).toLinearMap =
      (shearSLinear a).comp (shearTLinear f) := by
  apply LinearMap.ext
  intro u
  change adjoint a f u = (shearS a ∘ shearT f) u
  exact congrFun (adjoint_eq_shears a f) u

def shearSMatrix (a : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, a, 0; 0, 1, 0, a; 0, 0, 1, 0; 0, 0, 0, 1]

def shearTMatrix (f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; -f, 1, 0, 0; 0, 0, 1, 0; 0, 0, -f, 1]

theorem matrix_shearS (a : ℝ) :
    LinearMap.toMatrix' (shearSLinear a) = shearSMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix', shearSLinear,
    shearS, shearSMatrix, Pi.single_apply]

theorem matrix_shearT (f : ℝ) :
    LinearMap.toMatrix' (shearTLinear f) = shearTMatrix f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix', shearTLinear,
    shearT, shearTMatrix, Pi.single_apply]

theorem det_shearS (a : ℝ) : LinearMap.det (shearSLinear a) = 1 := by
  rw [← LinearMap.det_toMatrix', matrix_shearS]
  have ht : (shearSMatrix a).BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [shearSMatrix]
  rw [Matrix.det_of_upperTriangular ht]
  simp [shearSMatrix, Fin.prod_univ_succ]

theorem det_shearT (f : ℝ) : LinearMap.det (shearTLinear f) = 1 := by
  rw [← LinearMap.det_toMatrix', matrix_shearT, ← Matrix.det_transpose]
  have ht : (shearTMatrix f).transpose.BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [shearTMatrix, Matrix.transpose_apply]
  rw [Matrix.det_of_upperTriangular ht]
  simp [shearTMatrix, Matrix.transpose_apply, Fin.prod_univ_succ]

theorem det_adjoint (a f : ℝ) :
    LinearMap.det (adjointLinearEquiv a f).toLinearMap = 1 := by
  rw [adjoint_linear_factorization, LinearMap.det_comp, det_shearS, det_shearT]
  exact one_mul 1

theorem adjoint_preserves_haar (a f : ℝ) (μ : Measure Coordinates)
    [μ.IsAddHaarMeasure] : Measure.map (adjoint a f) μ = μ := by
  have hn : LinearMap.det (adjointLinearEquiv a f).toLinearMap ≠ 0 := by
    rw [det_adjoint]
    exact one_ne_zero
  have hm := Measure.map_linearMap_addHaar_pi_eq_smul_addHaar hn μ
  simpa only [det_adjoint, inv_one, abs_one, ENNReal.ofReal_one, one_smul] using hm

def leftMap (g : Frame) (u : Coordinates) : Frame :=
  originalUpperAffineComp g (embed u)

def rightMap (g : Frame) (u : Coordinates) : Frame :=
  originalUpperAffineComp (embed u) g

theorem measurable_rightMap (g : Frame) : Measurable (rightMap g) := by
  apply Continuous.measurable
  apply continuous_pi
  intro i
  fin_cases i <;> simp [rightMap, originalUpperAffineComp, embed] <;> fun_prop

theorem measurable_adjoint (a f : ℝ) : Measurable (adjoint a f) :=
  (adjointLinearEquiv a f).toLinearMap.continuous_of_finiteDimensional.measurable

def leftCoset (g : Frame) : Set Frame := (originalUpperAffineComp g) '' H

def rightCoset (g : Frame) : Set Frame := (fun h => originalUpperAffineComp h g) '' H

theorem leftCoset_eq_range (g : Frame) : leftCoset g = Set.range (leftMap g) := by
  ext z
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [← range_embed] at hh
    rcases hh with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨embed u, embed_mem u, rfl⟩

theorem rightCoset_eq_range (g : Frame) : rightCoset g = Set.range (rightMap g) := by
  ext z
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [← range_embed] at hh
    rcases hh with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨embed u, embed_mem u, rfl⟩

theorem coset_sets_equal (g : Frame) : leftCoset g = rightCoset g := by
  rw [leftCoset_eq_range, rightCoset_eq_range]
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨adjoint (g 0) (g 5) u, (actual_left_eq_right_adjoint g u).symm⟩
  · rintro ⟨u, rfl⟩
    refine ⟨(adjointLinearEquiv (g 0) (g 5)).symm u, ?_⟩
    change originalUpperAffineComp g (embed _) = _
    rw [actual_left_eq_right_adjoint]
    change originalUpperAffineComp
      (embed ((adjointLinearEquiv (g 0) (g 5))
        ((adjointLinearEquiv (g 0) (g 5)).symm u))) g = _
    rw [LinearEquiv.apply_symm_apply]
    rfl

/-- Complete I2330 coset distinction stage: arbitrary actual frame and every
fixed Haar normalization in the faithful additive chart of H. -/
theorem haar_coset_measure_stage (g : Frame) (μ : Measure Coordinates)
    [μ.IsAddHaarMeasure] :
    leftCoset g = rightCoset g ∧
      Measure.map (leftMap g) μ = Measure.map (rightMap g) μ := by
  refine ⟨coset_sets_equal g, ?_⟩
  have hfun : leftMap g = rightMap g ∘ adjoint (g 0) (g 5) := by
    funext u
    exact actual_left_eq_right_adjoint g u
  rw [hfun, ← Measure.map_map (measurable_rightMap g)
    (measurable_adjoint (g 0) (g 5)), adjoint_preserves_haar]

end PaperI.HaarCosetMeasure
