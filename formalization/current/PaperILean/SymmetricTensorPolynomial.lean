import PaperILean.PolynomialTensorSymmetry
import PaperILean.CoefficientJetBounds

/-! Actual symmetric multilinear tensors and their diagonal polynomials.
Symmetry means invariance under every slot permutation, as in the source.
The coordinate expansion includes all ordered words; no orbit is discarded.
-/

noncomputable section
open scoped BigOperators
namespace PaperI

abbrev TensorSpace (n : ℕ) := ContinuousMultilinearMap ℝ
  (fun _ : Fin n => PhysicalSpace) ℝ

def symmetricTensorSubmodule (n : ℕ) : Submodule ℝ (TensorSpace n) where
  carrier := {T | ∀ v : Fin n → PhysicalSpace, ∀ σ : Equiv.Perm (Fin n), T (v ∘ σ) = T v}
  zero_mem' := by simp
  add_mem' := by
    intro T S hT hS v σ
    simp only [ContinuousMultilinearMap.add_apply, hT v σ, hS v σ]
  smul_mem' := by
    intro a T hT v σ
    simp only [ContinuousMultilinearMap.smul_apply, hT v σ]

abbrev SymmetricTensor (n : ℕ) := symmetricTensorSubmodule n

theorem symmetricTensor_perm {n : ℕ} (T : SymmetricTensor n)
    (v : Fin n → PhysicalSpace) (σ : Equiv.Perm (Fin n)) :
    T.val (v ∘ σ) = T.val v := T.property v σ

theorem tensor_expand_coordinates {n : ℕ} (T : TensorSpace n)
    (v : Fin n → PhysicalSpace) :
    T v = ∑ a : Fin n → Fin 3,
      (∏ j, v j (a j)) * T (fun j => Pi.single (a j) (1 : ℝ)) := by
  classical
  have hv : (fun j : Fin n => ∑ i : Fin 3,
      v j i • (Pi.single i (1 : ℝ) : PhysicalSpace)) = v := by
    funext j i
    simp [Pi.single_apply]
  rw [← hv, T.map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [T.map_smul_univ]
  simp [Pi.single_apply, smul_eq_mul]

theorem tensor_eq_of_coordinates {n : ℕ} (T S : TensorSpace n)
    (h : ∀ a : Fin n → Fin 3, T (fun j => Pi.single (a j) (1 : ℝ)) =
      S (fun j => Pi.single (a j) (1 : ℝ))) : T = S := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [tensor_expand_coordinates, tensor_expand_coordinates]
  simp only [h]

def tensorDiagonalPolynomial {n : ℕ} (T : TensorSpace n) : MvPolynomial (Fin 3) ℝ :=
  ∑ a : Fin n → Fin 3,
    MvPolynomial.C (T (fun j => Pi.single (a j) (1 : ℝ))) *
      ∏ j, MvPolynomial.X (a j)

theorem eval_tensorDiagonalPolynomial {n : ℕ} (T : TensorSpace n) (x : PhysicalSpace) :
    MvPolynomial.eval x (tensorDiagonalPolynomial T) = T (fun _ => x) := by
  classical
  simp only [tensorDiagonalPolynomial, MvPolynomial.eval_sum, map_mul,
    MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  rw [tensor_expand_coordinates]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem totalDegree_tensorDiagonalPolynomial_le {n : ℕ} (T : TensorSpace n) :
    (tensorDiagonalPolynomial T).totalDegree ≤ n := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_finset_prod _ _).trans_eq (by simp)

theorem tensorDiagonalPolynomial_add {n : ℕ} (T S : TensorSpace n) :
    tensorDiagonalPolynomial (T + S) = tensorDiagonalPolynomial T + tensorDiagonalPolynomial S := by
  classical
  simp [tensorDiagonalPolynomial, map_add, add_mul, Finset.sum_add_distrib]

theorem tensorDiagonalPolynomial_smul {n : ℕ} (a : ℝ) (T : TensorSpace n) :
    tensorDiagonalPolynomial (a • T) = a • tensorDiagonalPolynomial T := by
  classical
  simp [tensorDiagonalPolynomial, MvPolynomial.smul_eq_C_mul, map_mul, mul_assoc,
    Finset.mul_sum]

def tensorSingletonSeries {n : ℕ} (T : TensorSpace n) :
    FormalMultilinearSeries ℝ PhysicalSpace ℝ :=
  fun m => if h : n = m then h ▸ T else 0

theorem tensor_diagonal_hasFiniteSeries {n : ℕ} (T : TensorSpace n) :
    HasFiniteFPowerSeriesOnBall (fun x : PhysicalSpace => T (fun _ => x))
      (tensorSingletonSeries T) 0 (n + 1) 1 := by
  classical
  apply HasFiniteFPowerSeriesOnBall.mk'
  · intro m hm
    have hnm : n ≠ m := by omega
    simp [tensorSingletonSeries, hnm]
  · norm_num
  · intro y _
    rw [Finset.sum_eq_single n]
    · simp [tensorSingletonSeries]
    · intro m _ hmn
      simp [tensorSingletonSeries, Ne.symm hmn]
    · intro hn
      exact (hn (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim

theorem tensor_diagonal_derivative_other {n m : ℕ} (T : TensorSpace n) (hmn : m ≠ n)
    (v : Fin m → PhysicalSpace) :
    iteratedFDeriv ℝ m (fun x : PhysicalSpace => T (fun _ => x)) 0 v = 0 := by
  rw [(tensor_diagonal_hasFiniteSeries T).toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace]
  simp [tensorSingletonSeries, Ne.symm hmn]

theorem symmetricTensor_diagonal_derivative {n : ℕ} (T : SymmetricTensor n)
    (v : Fin n → PhysicalSpace) :
    iteratedFDeriv ℝ n (fun x : PhysicalSpace => T.val (fun _ => x)) 0 v =
      (n.factorial : ℝ) * T.val v := by
  classical
  rw [(tensor_diagonal_hasFiniteSeries T.val).toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace]
  simp only [tensorSingletonSeries, ↓reduceDIte]
  have hp : ∀ σ : Equiv.Perm (Fin n), T.val (fun i => v (σ i)) = T.val v :=
    fun σ => symmetricTensor_perm T v σ
  simp only [hp, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

end PaperI
