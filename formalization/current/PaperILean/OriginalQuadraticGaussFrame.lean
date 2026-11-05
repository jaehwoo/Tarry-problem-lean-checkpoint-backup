import PaperILean.OriginalQuadraticGaussGraph
import PaperILean.OriginalGaussRelativeFrameIntegration

/-! I702-I717/I1293/I1305: exact quadratic reference frames in the original
Gauss normalization. Affine terms and root offset are retained. Relative
frames depend only on parameter differences, r and its Schur complement. -/
noncomputable section
namespace PaperI

def originalQuadraticInvariant (r b v t w : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  x 0-originalQuadraticGraph r b v t w 0 ![x 1,x 2]

def originalQuadraticGaussFrame (r b v t w η : ℝ) (a : Fin 2 → ℝ) : Fin 6 → ℝ :=
  originalGaussFrameField (originalQuadraticGraph r b v t w η)
    (originalQuadraticGaussInverse r b t) a

theorem originalQuadraticGaussFrame_formula (r b v t w η : ℝ) (a : Fin 2 → ℝ) :
    originalQuadraticGaussFrame r b v t w η a =
      originalGaussNormalFrame (a 0) (a 1)
        (originalQuadraticGraph r b v t w η ![originalQuadraticGaussInverse r b t a,a 1])
        (originalQuadraticGaussInverse r b t a)
        (b*originalQuadraticGaussInverse r b t a+v*a 1+w) (-b/r) := by
  simp [originalQuadraticGaussFrame,originalGaussFrameField,
    originalQuadraticGraph_Cz,originalQuadraticGraph_shear]

theorem originalQuadraticGaussFrame_origin (r b v t w η : ℝ) (a : Fin 2 → ℝ) :
    originalUpperAffineEval (originalQuadraticGaussFrame r b v t w η a) 0 =
      ![originalQuadraticGraph r b v t w η ![originalQuadraticGaussInverse r b t a,a 1],
        originalQuadraticGaussInverse r b t a,a 1] := by
  rw [originalQuadraticGaussFrame_formula,originalGaussNormalFrame_eval]
  simp

theorem originalQuadraticInvariant_frame (r b v t w η : ℝ) (hr : r ≠ 0)
    (a : Fin 2 → ℝ) (x : Fin 3 → ℝ) :
    originalQuadraticInvariant r b v t w
      (originalUpperAffineEval (originalQuadraticGaussFrame r b v t w η a) x) =
      η+x 0-r/2*(x 1)^2-originalQuadraticSchur r b v/2*(x 2)^2 := by
  rw [originalQuadraticGaussFrame_formula,originalGaussNormalFrame_eval]
  simp [originalQuadraticInvariant,originalQuadraticGraph,originalQuadraticGaussInverse,
    originalQuadraticSchur]
  field_simp
  ring

theorem originalQuadraticGraph_frozen (r b v t w η : ℝ) (hr : r ≠ 0)
    (a u : Fin 2 → ℝ) :
    originalGaussGraphPullback (originalQuadraticGaussFrame r b v t w η a)
      (originalQuadraticGraph r b v t w η) u =
      r/2*(u 0)^2+originalQuadraticSchur r b v/2*(u 1)^2 := by
  rw [originalQuadraticGaussFrame_formula]
  simp [originalGaussGraphPullback,originalGaussGraphBaseChange,originalGaussNormalFrame,
    originalQuadraticGraph,originalQuadraticGaussInverse,originalQuadraticSchur]
  field_simp
  ring

theorem originalQuadraticGaussFrame_relative (r b v t w η : ℝ) (hr : r ≠ 0)
    (a q : Fin 2 → ℝ) :
    originalUpperRelativeFrame (originalQuadraticGaussFrame r b v t w η a)
      (originalQuadraticGaussFrame r b v t w η q) =
      ![q 0-a 0,originalQuadraticSchur r b v*(q 1-a 1),
        (q 0-a 0)^2/(2*r)+originalQuadraticSchur r b v/2*(q 1-a 1)^2,
        0,(q 0-a 0)/r,q 1-a 1] := by
  rw [originalQuadraticGaussFrame_formula,originalQuadraticGaussFrame_formula]
  ext i
  fin_cases i <;>
    simp [originalUpperRelativeFrame,originalUpperAffineComp,originalUpperAffineInv,
      originalGaussNormalFrame,originalQuadraticGraph,originalQuadraticGaussInverse,
      originalQuadraticSchur] <;> (try field_simp) <;> ring

theorem originalQuadraticGaussFrame_relative_reverse (r b v t w η : ℝ) (hr : r ≠ 0)
    (a q : Fin 2 → ℝ) :
    originalUpperRelativeFrame (originalQuadraticGaussFrame r b v t w η q)
      (originalQuadraticGaussFrame r b v t w η a) =
      ![-(q 0-a 0),-originalQuadraticSchur r b v*(q 1-a 1),
        (q 0-a 0)^2/(2*r)+originalQuadraticSchur r b v/2*(q 1-a 1)^2,
        0,-(q 0-a 0)/r,-(q 1-a 1)] := by
  rw [originalQuadraticGaussFrame_relative r b v t w η hr q a]
  ext i
  fin_cases i <;> simp <;> ring

theorem originalQuadraticGaussFrame_global_chart (r b v t w η : ℝ) (hr : r ≠ 0) :
    Function.Bijective (fun a : Fin 2 → ℝ =>
      (![originalGaussCy (originalQuadraticGraph r b v t w η) a,a 1] : Fin 2 → ℝ)) := by
  constructor
  · intro a q h
    have h0 := congrArg (originalQuadraticGaussInverse r b t) h
    rw [originalQuadraticGaussInverse_left r b v t w η hr,
      originalQuadraticGaussInverse_left r b v t w η hr] at h0
    have h1 := congrFun h 1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  · intro a
    refine ⟨![originalQuadraticGaussInverse r b t a,a 1],?_⟩
    change (![originalGaussCy (originalQuadraticGraph r b v t w η)
      ![originalQuadraticGaussInverse r b t a,a 1],a 1] : Fin 2 → ℝ) = a
    rw [originalQuadraticGaussInverse_right r b v t w η hr]
    ext i
    fin_cases i <;> rfl

end PaperI
