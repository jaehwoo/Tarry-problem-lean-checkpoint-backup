import PaperILean.EllipsoidVolume
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! I327: the exact SO(3) neighborhood, its product and inverse inclusions.
The bundled determinant-one subgroup is explicitly identified with the pinned
specialOrthogonalGroup matrix set. All norms are the Euclidean operator norm.
The inverse estimate is algebraic norm absorption, not a new assumed series. -/
noncomputable section
open Set
open scoped Matrix Matrix.L2OpNorm Pointwise
namespace PaperI

def rotationGroup3 : Subgroup (Matrix.orthogonalGroup (Fin 3) ℝ) where
  carrier := {O | (O.val : Matrix (Fin 3) (Fin 3) ℝ).det = 1}
  one_mem' := by simp
  mul_mem' := by
    intro O P hO hP
    change (O.val * P.val).det = 1
    rw [Matrix.det_mul, hO, hP, one_mul]
  inv_mem' := by
    intro O hO
    change (star O.val).det = 1
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.det_transpose] using hO

def rotationMatrix (O : rotationGroup3) : Matrix (Fin 3) (Fin 3) ℝ := O.val.val

theorem rotationMatrix_one : rotationMatrix 1 = 1 := rfl

theorem rotationMatrix_mul (O P : rotationGroup3) :
    rotationMatrix (O * P) = rotationMatrix O * rotationMatrix P := rfl

theorem rotationMatrix_inv (O : rotationGroup3) :
    rotationMatrix O⁻¹ = (rotationMatrix O)ᵀ := by
  change star O.val.val = O.val.valᵀ
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

theorem rotationMatrix_orthogonal (O : rotationGroup3) :
    rotationMatrix O * (rotationMatrix O)ᵀ = 1 := by
  have h := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp O.val.property
  simpa only [rotationMatrix, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem rotationMatrix_det (O : rotationGroup3) : (rotationMatrix O).det = 1 := O.property

theorem rotationMatrix_mem_specialOrthogonalGroup (O : rotationGroup3) :
    rotationMatrix O ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨O.val.property, O.property⟩

theorem exists_rotationMatrix_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    (∃ O : rotationGroup3, rotationMatrix O = A) ↔
      A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  constructor
  · rintro ⟨O, rfl⟩; exact rotationMatrix_mem_specialOrthogonalGroup O
  · intro h
    exact ⟨⟨⟨A, h.1⟩, h.2⟩, rfl⟩

def frameConjugate (E : PositiveFrame) (A : Matrix (Fin 3) (Fin 3) ℝ) :=
  E.val⁻¹ * A * E.val

theorem frameConjugate_one (E : PositiveFrame) : frameConjugate E 1 = 1 := by
  simp only [frameConjugate, Matrix.mul_one, relativeFrame_initial]

theorem frameConjugate_mul (E : PositiveFrame) (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    frameConjugate E (A * B) = frameConjugate E A * frameConjugate E B := by
  have hi := Matrix.mul_nonsing_inv E.val (isUnit_iff_ne_zero.mpr E.property.ne')
  unfold frameConjugate
  calc
    E.val⁻¹ * (A * B) * E.val = E.val⁻¹ * A * (E.val * E.val⁻¹) * B * E.val := by rw [hi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem frameConjugate_sub (E : PositiveFrame) (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    frameConjugate E (A - B) = frameConjugate E A - frameConjugate E B := by
  simp only [frameConjugate, Matrix.mul_sub, Matrix.sub_mul]

theorem matrix_mul_sub_one_lt (A B : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ)
    (hA : ‖A - 1‖ < s) (hB : ‖B - 1‖ < t) :
    ‖A * B - 1‖ < s + t + s * t := by
  have hs : 0 ≤ s := (norm_nonneg _).trans hA.le
  have hex : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  rw [hex]
  have hn := (norm_add_le ((A-1)+(B-1)) ((A-1)*(B-1))).trans
    (add_le_add (norm_add_le (A-1) (B-1)) (norm_mul_le (A-1) (B-1)))
  have hp := mul_le_mul hA.le hB.le (norm_nonneg _) hs
  linarith

theorem matrix_inverse_sub_one_lt_of_mul_eq_one
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (ht : t < 1)
    (hAB : A * B = 1) (hA : ‖A - 1‖ < t) : ‖B - 1‖ < t / (1 - t) := by
  have hex : B - 1 = -(A - 1) * B := by
    rw [neg_mul, Matrix.sub_mul, Matrix.one_mul, hAB]
    abel
  have hn : ‖B - 1‖ ≤ ‖A - 1‖ * ‖B‖ := by
    conv_lhs => rw [hex]
    simpa only [norm_neg] using norm_mul_le (-(A - 1)) B
  have hB : ‖B‖ ≤ 1 + ‖B - 1‖ := by
    calc
      ‖B‖ = ‖1 + (B - 1)‖ := by congr 1; abel
      _ ≤ ‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖ + ‖B - 1‖ := norm_add_le _ _
      _ = _ := by rw [norm_one]
  have hstep : ‖B - 1‖ < t * (1 + ‖B - 1‖) :=
    (hn.trans (mul_le_mul_of_nonneg_left hB (norm_nonneg _))).trans_lt
      (mul_lt_mul_of_pos_right hA (by positivity))
  apply (lt_div_iff₀ (by linarith : 0 < 1 - t)).mpr
  nlinarith

def rotationNeighborhood (E : PositiveFrame) (t : ℝ) : Set rotationGroup3 :=
  {O | ‖frameConjugate E (rotationMatrix O - 1)‖ < t}

theorem mem_rotationNeighborhood_iff (E : PositiveFrame) (t : ℝ) (O : rotationGroup3) :
    O ∈ rotationNeighborhood E t ↔ ‖frameConjugate E (rotationMatrix O) - 1‖ < t := by
  simp only [rotationNeighborhood, mem_setOf_eq, frameConjugate_sub, frameConjugate_one]

theorem one_mem_rotationNeighborhood_iff (E : PositiveFrame) (t : ℝ) :
    (1 : rotationGroup3) ∈ rotationNeighborhood E t ↔ 0 < t := by
  rw [mem_rotationNeighborhood_iff, rotationMatrix_one, frameConjugate_one, sub_self, norm_zero]

theorem rotationNeighborhood_empty_of_nonpos (E : PositiveFrame) (t : ℝ) (ht : t ≤ 0) :
    rotationNeighborhood E t = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro O hO
  exact (not_lt_of_ge ((norm_nonneg _).trans' ht)) hO

theorem rotationNeighborhood_mono (E : PositiveFrame) {s t : ℝ} (h : s ≤ t) :
    rotationNeighborhood E s ⊆ rotationNeighborhood E t := fun _ hO => hO.trans_le h

theorem rotationNeighborhood_mul_mem (E : PositiveFrame) (s t : ℝ)
    (O P : rotationGroup3) (hO : O ∈ rotationNeighborhood E s)
    (hP : P ∈ rotationNeighborhood E t) :
    O * P ∈ rotationNeighborhood E (s + t + s * t) := by
  rw [mem_rotationNeighborhood_iff, rotationMatrix_mul, frameConjugate_mul]
  exact matrix_mul_sub_one_lt _ _ s t
    ((mem_rotationNeighborhood_iff E s O).mp hO) ((mem_rotationNeighborhood_iff E t P).mp hP)

theorem rotationNeighborhood_mul_subset (E : PositiveFrame) (t : ℝ) :
    rotationNeighborhood E t * rotationNeighborhood E t ⊆ rotationNeighborhood E (2 * t + t ^ 2) := by
  rintro _ ⟨O, hO, P, hP, rfl⟩
  simpa only [two_mul, pow_two] using rotationNeighborhood_mul_mem E t t O P hO hP

theorem rotationNeighborhood_inv_mem (E : PositiveFrame) (t : ℝ) (ht : t < 1)
    (O : rotationGroup3) (hO : O ∈ rotationNeighborhood E t) :
    O⁻¹ ∈ rotationNeighborhood E (t / (1 - t)) := by
  rw [mem_rotationNeighborhood_iff]
  apply matrix_inverse_sub_one_lt_of_mul_eq_one _ _ t ht
  · rw [← frameConjugate_mul, ← rotationMatrix_mul, mul_inv_cancel, rotationMatrix_one,
      frameConjugate_one]
  · exact (mem_rotationNeighborhood_iff E t O).mp hO

theorem rotationNeighborhood_inv_subset (E : PositiveFrame) (t : ℝ) (ht : t < 1) :
    (rotationNeighborhood E t)⁻¹ ⊆ rotationNeighborhood E (t / (1 - t)) := by
  intro O hO
  have h := rotationNeighborhood_inv_mem E t ht O⁻¹ (Set.mem_inv.mp hO)
  simpa only [inv_inv] using h

theorem rotationNeighborhood_relative_of_left_intersection
    (E : PositiveFrame) (t : ℝ) (ht : t < 1) (O P u v : rotationGroup3)
    (hu : u ∈ rotationNeighborhood E t) (hv : v ∈ rotationNeighborhood E t)
    (hx : O * u = P * v) :
    O⁻¹ * P ∈ rotationNeighborhood E (2 * t / (1 - t)) := by
  have heq : O⁻¹ * P = u * v⁻¹ := by
    calc
      O⁻¹ * P = O⁻¹ * (P * v) * v⁻¹ := by simp only [mul_assoc, mul_inv_cancel, mul_one]
      _ = u * v⁻¹ := by rw [← hx]; group
  rw [heq]
  have h := rotationNeighborhood_mul_mem E t (t/(1-t)) u v⁻¹ hu
    (rotationNeighborhood_inv_mem E t ht v hv)
  have hden : 1 - t ≠ 0 := by linarith
  convert h using 1 <;> field_simp <;> ring

end PaperI
