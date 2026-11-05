import PaperILean.OriginalHaarWindowSubgroups
import PaperILean.SingularValueEuclideanBounds

/-! Literal least-singular-value interpretation of the original physical
phase-only pivot on each of the three source subgroup Lie algebras. The
coordinate embeddings are Euclidean isometries, not changing physical frames. -/
noncomputable section
namespace PaperI
open Matrix
open scoped BigOperators

def originalHaarLieDimPred : OriginalHaarSubgroup → ℕ
  | .H0 => 3
  | .H3 => 2
  | .H => 3

abbrev OriginalHaarLieCoordinates (K : OriginalHaarSubgroup) :=
  Fin (originalHaarLieDimPred K+1) → ℝ

def originalHaarLieEmbed : (K : OriginalHaarSubgroup) → OriginalHaarLieCoordinates K → (Fin 6 → ℝ)
  | .H0,v => ![v 0,v 1,v 2,v 3,0,0]
  | .H3,v => ![v 0,v 1,v 2,0,0,0]
  | .H,v => ![0,v 0,v 1,v 2,v 3,0]

def originalHaarLieProject : (K : OriginalHaarSubgroup) → (Fin 6 → ℝ) → OriginalHaarLieCoordinates K
  | .H0,v => ![v 0,v 1,v 2,v 3]
  | .H3,v => ![v 0,v 1,v 2]
  | .H,v => ![v 1,v 2,v 3,v 4]

def originalHaarLieEmbedLinear (K : OriginalHaarSubgroup) :
    OriginalHaarLieCoordinates K →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun := originalHaarLieEmbed K
  map_add' u v := by cases K <;> ext i <;> fin_cases i <;> simp [originalHaarLieEmbed]
  map_smul' c u := by cases K <;> ext i <;> fin_cases i <;> simp [originalHaarLieEmbed]

theorem originalHaarLieEmbed_project (K : OriginalHaarSubgroup) (v : Fin 6 → ℝ)
    (hv : v ∈ originalHaarSubgroupSet K) :
    originalHaarLieEmbed K (originalHaarLieProject K v) = v := by
  cases K <;> ext i <;> fin_cases i <;>
    simp_all [originalHaarLieEmbed,originalHaarLieProject,originalHaarSubgroupSet]

theorem originalHaarLieEmbed_norm (K : OriginalHaarSubgroup) (v : OriginalHaarLieCoordinates K) :
    coordinateL2Norm (originalHaarLieEmbed K v) = coordinateL2Norm v := by
  cases K <;> simp [coordinateL2Norm,originalHaarLieEmbed,originalHaarLieDimPred,Fin.sum_univ_succ]
  <;> congr 1 <;> ring

def originalHaarPhysicalLieLinear {k : ℕ} (J : CoefficientSpace k) :
    (Fin 6 → ℝ) →ₗ[ℝ] CoefficientSpace k where
  toFun := originalHaarPhysicalLieAction J
  map_add' u v := by
    simp [originalHaarPhysicalLieAction,upperAffineFieldTranslation_add,
      upperAffineFieldLinear_add,affineFieldCoefficientMap_add_field]
  map_smul' c u := by
    simp [originalHaarPhysicalLieAction,upperAffineFieldTranslation_smul,
      upperAffineFieldLinear_smul,affineFieldCoefficientMap_smul_field]

def originalHaarPhysicalOrbitMatrix {k : ℕ} (K : OriginalHaarSubgroup) (J : CoefficientSpace k) :
    Matrix (MonomialIndex k) (Fin (originalHaarLieDimPred K+1)) ℝ :=
  LinearMap.toMatrix' ((originalHaarPhysicalLieLinear J).comp (originalHaarLieEmbedLinear K))

/-- The literal R_J^ph restricted to an orthonormal basis of LieK. -/
def originalHaarPhysicalLeastSingularValue {k : ℕ} (K : OriginalHaarSubgroup)
    (J : CoefficientSpace k) : ℝ :=
  descendingSingularValues (originalHaarPhysicalOrbitMatrix K J) (Fin.last (originalHaarLieDimPred K))

theorem originalHaarPhysicalOrbitMatrix_mulVec {k : ℕ} (K : OriginalHaarSubgroup)
    (J : CoefficientSpace k) (v : OriginalHaarLieCoordinates K) :
    originalHaarPhysicalOrbitMatrix K J *ᵥ v =
      originalHaarPhysicalLieAction J (originalHaarLieEmbed K v) := by
  exact congrArg (fun L : OriginalHaarLieCoordinates K →ₗ[ℝ] CoefficientSpace k => L v)
    (Matrix.toLin'_toMatrix' ((originalHaarPhysicalLieLinear J).comp (originalHaarLieEmbedLinear K)))

/-- The source least singular value bounds every actual physical subgroup
body direction, in the original Euclidean norms. -/
theorem originalHaarPhysicalLeastSingularValue_mul_norm_le {k : ℕ}
    (K : OriginalHaarSubgroup) (J : CoefficientSpace k) (v : Fin 6 → ℝ)
    (hv : v ∈ originalHaarSubgroupSet K) :
    originalHaarPhysicalLeastSingularValue K J*coordinateL2Norm v ≤
      coefficientEuclideanNorm (originalHaarPhysicalLieAction J v) := by
  let w := originalHaarLieProject K v
  let x : EuclideanSpace ℝ (Fin (originalHaarLieDimPred K+1)) :=
    (WithLp.linearEquiv 2 ℝ (OriginalHaarLieCoordinates K)).symm w
  have h := least_descendingSingularValue_mul_norm_le (originalHaarPhysicalOrbitMatrix K J) x
  have hx : ‖x‖=coordinateL2Norm v := by
    rw [← coordinateL2Norm_eq_norm]
    rw [← originalHaarLieEmbed_norm K w,originalHaarLieEmbed_project K v hv]
  have hAx : ‖Matrix.toEuclideanLin (originalHaarPhysicalOrbitMatrix K J) x‖ =
      coefficientEuclideanNorm (originalHaarPhysicalLieAction J v) := by
    rw [coefficientEuclideanNorm_eq_norm]
    congr 1
    apply PiLp.ext
    intro α
    change (originalHaarPhysicalOrbitMatrix K J *ᵥ w) α = originalHaarPhysicalLieAction J v α
    rw [originalHaarPhysicalOrbitMatrix_mulVec,originalHaarLieEmbed_project K v hv]
  rw [hx,hAx] at h
  exact h

/-- The exact printed s_min>=P^(-c) hypothesis supplies the inverse bound
used in the original path argument, for arbitrary real c and P>0. -/
theorem originalHaar_literal_pivot_inverse_bound {k : ℕ}
    (K : OriginalHaarSubgroup) (J : CoefficientSpace k) (P c : ℝ) (hP : 0<P)
    (hpiv : P^(-c) ≤ originalHaarPhysicalLeastSingularValue K J)
    (v : Fin 6 → ℝ) (hv : v ∈ originalHaarSubgroupSet K) :
    coordinateL2Norm v ≤ P^c*coefficientEuclideanNorm (originalHaarPhysicalLieAction J v) := by
  have h := (mul_le_mul_of_nonneg_right hpiv (coordinateL2Norm_nonneg v)).trans
    (originalHaarPhysicalLeastSingularValue_mul_norm_le K J v hv)
  have hPc : 0 ≤ P^c := (Real.rpow_pos_of_pos hP c).le
  have he : P^c*P^(-c)=1 := by rw [← Real.rpow_add hP]; simp
  calc
    coordinateL2Norm v = P^c*(P^(-c)*coordinateL2Norm v) := by rw [← mul_assoc,he,one_mul]
    _ ≤ P^c*coefficientEuclideanNorm (originalHaarPhysicalLieAction J v) :=
      mul_le_mul_of_nonneg_left h hPc

end PaperI
