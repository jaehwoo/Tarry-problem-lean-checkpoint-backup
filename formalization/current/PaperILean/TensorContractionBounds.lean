import PaperILean.SymmetricTensorPolynomial
import PaperILean.CompleteJetTaylorTransport
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.NormedSpace.Multilinear.Curry

/-! Euclidean / full ordered-component Hilbert--Schmidt contraction bounds.
No operator norm replaces the displayed HS norm. These inequalities hold for
arbitrary tensors, including nonsymmetric ones, and in degree zero.
-/

noncomputable section
open scoped BigOperators
namespace PaperI

def coordinateL2Norm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (v i) ^ 2)

theorem coordinateL2Norm_eq_norm {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    coordinateL2Norm v = ‖(WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm v‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [coordinateL2Norm, Real.norm_eq_abs, sq_abs]

theorem coordinateL2Norm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    0 ≤ coordinateL2Norm v := Real.sqrt_nonneg _

theorem coordinateL2Norm_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    (coordinateL2Norm v) ^ 2 = ∑ i, (v i) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem coordinateL2Norm_smul {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) :
    coordinateL2Norm (a • v) = |a| * coordinateL2Norm v := by
  simp only [coordinateL2Norm_eq_norm, map_smul, norm_smul, Real.norm_eq_abs]

theorem coordinateL2Norm_sum_le {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (v : κ → ι → ℝ) :
    coordinateL2Norm (∑ j ∈ s, v j) ≤ ∑ j ∈ s, coordinateL2Norm (v j) := by
  simp only [coordinateL2Norm_eq_norm, map_sum]
  exact norm_sum_le _ _

def physicalEuclideanNorm (h : PhysicalSpace) : ℝ := coordinateL2Norm h

theorem physicalEuclideanNorm_nonneg (h : PhysicalSpace) :
    0 ≤ physicalEuclideanNorm h := coordinateL2Norm_nonneg h

def tensorCoordinates {n : ℕ} (T : TensorSpace n) : (Fin n → Fin 3) → ℝ :=
  fun a => T (fun j => Pi.single (a j) (1 : ℝ))

def tensorHSNorm {n : ℕ} (T : TensorSpace n) : ℝ :=
  coordinateL2Norm (tensorCoordinates T)

theorem tensorHSNorm_nonneg {n : ℕ} (T : TensorSpace n) :
    0 ≤ tensorHSNorm T := coordinateL2Norm_nonneg _

theorem tensorHSNorm_sq {n : ℕ} (T : TensorSpace n) :
    (tensorHSNorm T) ^ 2 = ∑ a : Fin n → Fin 3, (tensorCoordinates T a) ^ 2 :=
  coordinateL2Norm_sq _

theorem tensorHSNorm_smul {n : ℕ} (a : ℝ) (T : TensorSpace n) :
    tensorHSNorm (a • T) = |a| * tensorHSNorm T := by
  change coordinateL2Norm (a • tensorCoordinates T) = _
  exact coordinateL2Norm_smul a _

theorem tensorHSNorm_sum_le {n : ℕ} {κ : Type*} (s : Finset κ)
    (T : κ → TensorSpace n) :
    tensorHSNorm (∑ j ∈ s, T j) ≤ ∑ j ∈ s, tensorHSNorm (T j) := by
  have heq : tensorCoordinates (∑ j ∈ s, T j) = ∑ j ∈ s, tensorCoordinates (T j) := by
    funext a
    simp [tensorCoordinates]
  unfold tensorHSNorm
  rw [heq]
  exact coordinateL2Norm_sum_le s _

def tensorWordHeadTailEquiv (n : ℕ) :
    (Fin (n + 1) → Fin 3) ≃ Fin 3 × (Fin n → Fin 3) where
  toFun a := (a 0, Fin.tail a)
  invFun p := Fin.cons p.1 p.2
  left_inv a := Fin.cons_self_tail a
  right_inv p := by simp

theorem tensorCoordinates_cons {n : ℕ} (T : TensorSpace (n + 1))
    (i : Fin 3) (a : Fin n → Fin 3) :
    tensorCoordinates T (Fin.cons i a) =
      T (Fin.cons (Pi.single i (1 : ℝ)) (fun j => Pi.single (a j) (1 : ℝ))) := by
  unfold tensorCoordinates
  congr 1
  funext j
  refine Fin.cases ?_ (fun l => ?_) j <;> simp

theorem tensorHSNorm_sq_split {n : ℕ} (T : TensorSpace (n + 1)) :
    (tensorHSNorm T) ^ 2 =
      ∑ a : Fin n → Fin 3, ∑ i : Fin 3, (tensorCoordinates T (Fin.cons i a)) ^ 2 := by
  rw [tensorHSNorm_sq]
  have he := (tensorWordHeadTailEquiv n).symm.sum_comp
    (fun a => (tensorCoordinates T a) ^ 2)
  rw [← he]
  change (∑ p : Fin 3 × (Fin n → Fin 3),
    (tensorCoordinates T (Fin.cons p.1 p.2)) ^ 2) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem tensor_curryLeft_coordinates {n : ℕ} (T : TensorSpace (n + 1))
    (h : PhysicalSpace) (a : Fin n → Fin 3) :
    tensorCoordinates (T.curryLeft h) a =
      ∑ i : Fin 3, h i * tensorCoordinates T (Fin.cons i a) := by
  classical
  have hh : h = ∑ i : Fin 3, h i • (Pi.single i (1 : ℝ) : PhysicalSpace) := by
    funext i
    simp [Pi.single_apply]
  conv_lhs => rw [hh]
  simp only [map_sum, map_smul, tensorCoordinates,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.curryLeft_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun t => h i * t) (tensorCoordinates_cons T i a).symm

theorem tensorHSNorm_curryLeft_le {n : ℕ} (T : TensorSpace (n + 1))
    (h : PhysicalSpace) :
    tensorHSNorm (T.curryLeft h) ≤ physicalEuclideanNorm h * tensorHSNorm T := by
  have hsq : (tensorHSNorm (T.curryLeft h)) ^ 2 ≤
      (physicalEuclideanNorm h) ^ 2 * (tensorHSNorm T) ^ 2 := by
    rw [tensorHSNorm_sq, tensorHSNorm_sq_split]
    unfold physicalEuclideanNorm
    rw [coordinateL2Norm_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    rw [tensor_curryLeft_coordinates]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ h
      (fun i => tensorCoordinates T (Fin.cons i a))
  apply (sq_le_sq₀ (tensorHSNorm_nonneg _) (mul_nonneg
    (physicalEuclideanNorm_nonneg h) (tensorHSNorm_nonneg T))).mp
  simpa only [mul_pow] using hsq

def tensorContractRepeated : (m r : ℕ) → TensorSpace (r + m) → PhysicalSpace → TensorSpace r
  | 0, _, T, _ => T
  | m + 1, r, T, h => tensorContractRepeated m r (T.curryLeft h) h

theorem tensorContractRepeated_apply (m r : ℕ) (T : TensorSpace (r + m))
    (h : PhysicalSpace) (v : Fin r → PhysicalSpace) :
    tensorContractRepeated m r T h v = T (prependDirections m r (fun _ => h) v) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [tensorContractRepeated, ih]
    rfl

theorem tensorHSNorm_contractRepeated_le (m r : ℕ) (T : TensorSpace (r + m))
    (h : PhysicalSpace) :
    tensorHSNorm (tensorContractRepeated m r T h) ≤
      physicalEuclideanNorm h ^ m * tensorHSNorm T := by
  induction m with
  | zero => simp [tensorContractRepeated]
  | succ m ih =>
    calc
      tensorHSNorm (tensorContractRepeated (m + 1) r T h) ≤
          physicalEuclideanNorm h ^ m * tensorHSNorm (T.curryLeft h) := ih _
      _ ≤ physicalEuclideanNorm h ^ m * (physicalEuclideanNorm h * tensorHSNorm T) :=
        mul_le_mul_of_nonneg_left (tensorHSNorm_curryLeft_le T h)
          (pow_nonneg (physicalEuclideanNorm_nonneg h) m)
      _ = physicalEuclideanNorm h ^ (m + 1) * tensorHSNorm T := by rw [pow_succ]; ring

end PaperI
