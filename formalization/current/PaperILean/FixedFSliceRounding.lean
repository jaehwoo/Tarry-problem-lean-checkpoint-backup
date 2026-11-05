import PaperILean.OriginalUpperBodyFlow
import Mathlib.Algebra.Order.Floor.Ring

/-! Disjoint bounded right patches in an original fixed-f slice.
The triangular integer rounding removes the actual upper-affine shears. -/

noncomputable section
namespace PaperI.FixedFSliceRounding

def meshRound (eps x : ℝ) : ℝ := eps * (⌊x / eps⌋ : ℝ)

def triIndex (eps : ℝ) (x : Fin 6 → ℝ) : Fin 5 → ℤ :=
  ![⌊x 0 / eps⌋,
    ⌊(x 1 - meshRound eps (x 0) * (x 3 - meshRound eps (x 3))) / eps⌋,
    ⌊(x 2 - meshRound eps (x 0) * (x 4 - meshRound eps (x 4))) / eps⌋,
    ⌊x 3 / eps⌋, ⌊x 4 / eps⌋]

def latticeCenter (eps F : ℝ) (z : Fin 5 → ℤ) : Fin 6 → ℝ :=
  ![eps * z 0, eps * z 1, eps * z 2, eps * z 3, eps * z 4, F]

def InRightCube (eps : ℝ) (r : Fin 6 → ℝ) : Prop :=
  (∀ i : Fin 5, 0 ≤ r i.castSucc ∧ r i.castSucc < eps) ∧ r 5 = 0

theorem meshRound_residual (eps x : ℝ) (heps : 0 < eps) :
    0 ≤ x - meshRound eps x ∧ x - meshRound eps x < eps := by
  have hlo := (le_div_iff₀ heps).mp (Int.floor_le (x / eps))
  have hhi := (div_lt_iff₀ heps).mp (Int.lt_floor_add_one (x / eps))
  dsimp [meshRound]
  constructor <;> nlinarith only [hlo, hhi]

theorem abs_meshRound_le (eps x : ℝ) (heps : 0 < eps) :
    |meshRound eps x| ≤ |x| + eps := by
  have hr := meshRound_residual eps x heps
  have hres : |x - meshRound eps x| ≤ eps := by
    rw [abs_of_nonneg hr.1]
    exact hr.2.le
  calc
    |meshRound eps x| = |x - (x - meshRound eps x)| := by congr 1; ring
    _ ≤ |x| + |x - meshRound eps x| := abs_sub _ _
    _ ≤ |x| + eps := add_le_add_left hres _

@[simp] theorem latticeCenter_fixed_f (eps F : ℝ) (z : Fin 5 → ℤ) :
    latticeCenter eps F z 5 = F := rfl

theorem latticeCenter_triIndex (eps F : ℝ) (x : Fin 6 → ℝ) :
    latticeCenter eps F (triIndex eps x) =
      ![meshRound eps (x 0),
        meshRound eps (x 1 - meshRound eps (x 0) * (x 3 - meshRound eps (x 3))),
        meshRound eps (x 2 - meshRound eps (x 0) * (x 4 - meshRound eps (x 4))),
        meshRound eps (x 3), meshRound eps (x 4), F] := by
  ext i
  fin_cases i <;> rfl

/-- At fixed original f the apparent terms involving that level cancel. -/
theorem relative_at_fixed_f (eps F : ℝ) (x : Fin 6 → ℝ) (z : Fin 5 → ℤ)
    (hf : x 5 = F) :
    originalUpperRelativeFrame (latticeCenter eps F z) x =
      ![x 0 - eps * z 0,
        x 1 - eps * z 1 - eps * z 0 * (x 3 - eps * z 3),
        x 2 - eps * z 2 - eps * z 0 * (x 4 - eps * z 4),
        x 3 - eps * z 3, x 4 - eps * z 4, 0] := by
  ext i
  fin_cases i <;>
    simp [originalUpperRelativeFrame, originalUpperAffineComp,
      originalUpperAffineInv, latticeCenter, hf] <;> ring

/-- Every point of the fixed-f slice lies in its rounded right cube. -/
theorem rounded_relative_mem (eps F : ℝ) (x : Fin 6 → ℝ)
    (heps : 0 < eps) (hf : x 5 = F) :
    InRightCube eps
      (originalUpperRelativeFrame (latticeCenter eps F (triIndex eps x)) x) := by
  rw [relative_at_fixed_f eps F x _ hf]
  constructor
  · intro i
    fin_cases i
    · simpa [triIndex, meshRound] using meshRound_residual eps (x 0) heps
    · convert meshRound_residual eps
        (x 1 - meshRound eps (x 0) * (x 3 - meshRound eps (x 3))) heps using 1 <;>
        simp [triIndex, meshRound] <;> ring_nf <;> constructor <;> intro h <;> linarith only [h]
    · convert meshRound_residual eps
        (x 2 - meshRound eps (x 0) * (x 4 - meshRound eps (x 4))) heps using 1 <;>
        simp [triIndex, meshRound] <;> ring_nf <;> constructor <;> intro h <;> linarith only [h]
    · simpa [triIndex, meshRound] using meshRound_residual eps (x 3) heps
    · simpa [triIndex, meshRound] using meshRound_residual eps (x 4) heps
  · rfl

private theorem floor_eq_of_residual (eps x : ℝ) (z : ℤ) (heps : 0 < eps)
    (hr : 0 ≤ x - eps * z ∧ x - eps * z < eps) : ⌊x / eps⌋ = z := by
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ heps).mpr
    nlinarith only [hr.1]
  · apply (div_lt_iff₀ heps).mpr
    nlinarith only [hr.2]

/-- Half-open right cubes with distinct lattice indices cannot overlap. -/
theorem right_cube_index_unique (eps F : ℝ) (x : Fin 6 → ℝ) (z : Fin 5 → ℤ)
    (heps : 0 < eps) (hf : x 5 = F)
    (hcube : InRightCube eps (originalUpperRelativeFrame (latticeCenter eps F z) x)) :
    z = triIndex eps x := by
  rw [relative_at_fixed_f eps F x z hf] at hcube
  have ha : ⌊x 0 / eps⌋ = z 0 :=
    floor_eq_of_residual eps (x 0) (z 0) heps (hcube.1 0)
  have hd : ⌊x 3 / eps⌋ = z 3 :=
    floor_eq_of_residual eps (x 3) (z 3) heps (hcube.1 3)
  have he : ⌊x 4 / eps⌋ = z 4 :=
    floor_eq_of_residual eps (x 4) (z 4) heps (hcube.1 4)
  have hb : ⌊(x 1 - eps * z 0 * (x 3 - eps * z 3)) / eps⌋ = z 1 := by
    apply floor_eq_of_residual eps _ (z 1) heps
    convert hcube.1 1 using 1 <;> simp <;> ring_nf <;> constructor <;> intro h <;> linarith only [h]
  have hc : ⌊(x 2 - eps * z 0 * (x 4 - eps * z 4)) / eps⌋ = z 2 := by
    apply floor_eq_of_residual eps _ (z 2) heps
    convert hcube.1 2 using 1 <;> simp <;> ring_nf <;> constructor <;> intro h <;> linarith only [h]
  ext i
  fin_cases i <;> simp [triIndex, meshRound, ha, hd, he, hb, hc]

end PaperI.FixedFSliceRounding
