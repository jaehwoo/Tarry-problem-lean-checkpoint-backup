import PaperILean.MatrixLogContinuity
import Mathlib.Topology.PartialHomeomorph

/-! I327/331: the exact inherited topology and fixed coordinate maps.
No replacement rotation group, coordinate measure or anisotropic norm is used. -/
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem rotationMatrix_continuous : Continuous rotationMatrix :=
  continuous_subtype_val.comp continuous_subtype_val

theorem rotationGroup3_continuous_mul :
    Continuous (fun p : rotationGroup3 × rotationGroup3 => p.1*p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (rotationMatrix_continuous.comp continuous_fst).mul
    (rotationMatrix_continuous.comp continuous_snd)

theorem rotationGroup3_continuous_inv : Continuous (fun O : rotationGroup3 => O⁻¹) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  simpa only [rotationMatrix_inv] using rotationMatrix_continuous.matrix_transpose

theorem rotationGroup3_isTopologicalGroup : IsTopologicalGroup rotationGroup3 where
  continuous_mul := rotationGroup3_continuous_mul
  continuous_inv := rotationGroup3_continuous_inv

attribute [instance] rotationGroup3_isTopologicalGroup

def rotationGroup3MeasurableSpace : MeasurableSpace rotationGroup3 := borel rotationGroup3

attribute [instance] rotationGroup3MeasurableSpace

theorem rotationGroup3_borelSpace : BorelSpace rotationGroup3 := ⟨rfl⟩

attribute [instance] rotationGroup3_borelSpace

def skewMatrixCoordinatesLinear : PhysicalSpace →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ where
  toFun := skewMatrixOfCoordinates
  map_add' := by
    intro x y
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrixOfCoordinates, add_comm]
  map_smul' := by
    intro r x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrixOfCoordinates]

def skewMatrixCoordinatesCLM : PhysicalSpace →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toContinuousLinearMap skewMatrixCoordinatesLinear

theorem skewMatrixCoordinatesCLM_apply (x : PhysicalSpace) :
    skewMatrixCoordinatesCLM x = skewMatrixOfCoordinates x := rfl

theorem skewMatrixOfCoordinates_continuous : Continuous skewMatrixOfCoordinates :=
  skewMatrixCoordinatesCLM.continuous

theorem skewMatrixOfCoordinates_zero : skewMatrixOfCoordinates 0 = 0 :=
  skewMatrixCoordinatesLinear.map_zero

theorem skewMatrixOfCoordinates_injective : Function.Injective skewMatrixOfCoordinates :=
  Function.LeftInverse.injective skewCoordinatesOfMatrix_left_inverse

def skewCoordinatesMatrixLinear : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] PhysicalSpace where
  toFun := skewCoordinatesOfMatrix
  map_add' := by intro A B; ext i; fin_cases i <;> rfl
  map_smul' := by intro r A; ext i; fin_cases i <;> rfl

def skewCoordinatesMatrixCLM : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] PhysicalSpace :=
  LinearMap.toContinuousLinearMap skewCoordinatesMatrixLinear

theorem skewCoordinatesMatrixCLM_apply (A : Matrix (Fin 3) (Fin 3) ℝ) :
    skewCoordinatesMatrixCLM A = skewCoordinatesOfMatrix A := rfl

theorem skewCoordinatesOfMatrix_continuous : Continuous skewCoordinatesOfMatrix :=
  skewCoordinatesMatrixCLM.continuous

def rotationCoordinateExp (x : PhysicalSpace) : rotationGroup3 :=
  skewRotationExp (skewMatrixOfCoordinates x) (skewMatrixOfCoordinates_skew x)

def rotationCoordinateLog (O : rotationGroup3) : PhysicalSpace :=
  skewCoordinatesOfMatrix (rotationLogSeries O)

theorem rotationMatrix_coordinateExp (x : PhysicalSpace) :
    rotationMatrix (rotationCoordinateExp x) = NormedSpace.exp ℝ (skewMatrixOfCoordinates x) := rfl

theorem rotationCoordinateExp_continuous : Continuous rotationCoordinateExp := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact NormedSpace.exp_continuous.comp skewMatrixOfCoordinates_continuous

theorem rotationCoordinateExp_zero : rotationCoordinateExp 0 = 1 := by
  apply rotationMatrix_injective
  simp only [rotationMatrix_coordinateExp, skewMatrixOfCoordinates_zero,
    NormedSpace.exp_zero, rotationMatrix_one]

theorem rotationLogSeries_continuousAt (O : rotationGroup3)
    (hO : ‖rotationMatrix O-1‖ < 1) : ContinuousAt rotationLogSeries O :=
  (matrixLogSeries_continuousAt _ hO).comp rotationMatrix_continuous.continuousAt

theorem rotationCoordinateLog_continuousAt (O : rotationGroup3)
    (hO : ‖rotationMatrix O-1‖ < 1) : ContinuousAt rotationCoordinateLog O :=
  skewCoordinatesOfMatrix_continuous.continuousAt.comp (rotationLogSeries_continuousAt O hO)

theorem rotationNeighborhood_isOpen (E : PositiveFrame) (t : ℝ) :
    IsOpen (rotationNeighborhood E t) := by
  apply isOpen_lt _ continuous_const
  exact ((frameConjugateCLM E).continuous.comp
    (rotationMatrix_continuous.sub continuous_const)).norm

theorem rotationNeighborhood_measurableSet (E : PositiveFrame) (t : ℝ) :
    MeasurableSet (rotationNeighborhood E t) := (rotationNeighborhood_isOpen E t).measurableSet

end PaperI
