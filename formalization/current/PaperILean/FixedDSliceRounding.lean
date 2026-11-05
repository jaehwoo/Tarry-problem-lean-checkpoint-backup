import PaperILean.FixedFSliceRounding
import PaperILean.OriginalDGaugeBox

/-! The fixed-d part of the original slice-net construction used in I1523.
The five free coordinates are rounded in the original group law. The source
box is an input to this geometric stage; no path or scale selection is assumed. -/
noncomputable section
namespace PaperI.FixedDSliceRounding
open FixedFSliceRounding

def sliceCoord : Fin 5 → Fin 6 := ![0,1,2,4,5]

def sliceWeight (H U W : ℝ) : Fin 5 → ℝ := ![U,H*U,H*U*W,H*W,W]

def eArgument (eps t : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  x 4 - t * (x 5 - meshRound eps (x 5))

def cArgument (eps t : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  x 2 - meshRound eps (x 0) * (eArgument eps t x - meshRound eps (eArgument eps t x)) -
    meshRound eps (x 1) * (x 5 - meshRound eps (x 5))

def triIndex (eps t : ℝ) (x : Fin 6 → ℝ) : Fin 5 → ℤ :=
  ![⌊x 0 / eps⌋,⌊x 1 / eps⌋,⌊cArgument eps t x / eps⌋,
    ⌊eArgument eps t x / eps⌋,⌊x 5 / eps⌋]

def latticeCenter (eps t : ℝ) (z : Fin 5 → ℤ) : Fin 6 → ℝ :=
  ![eps*z 0,eps*z 1,eps*z 2,t,eps*z 3,eps*z 4]

def InRightDCube (eps : ℝ) (r : Fin 6 → ℝ) : Prop :=
  (∀ i : Fin 5, 0 ≤ r (sliceCoord i) ∧ r (sliceCoord i) < eps) ∧ r 3 = 0

@[simp] theorem latticeCenter_fixed_d (eps t : ℝ) (z : Fin 5 → ℤ) :
    latticeCenter eps t z 3 = t := rfl

theorem latticeCenter_triIndex (eps t : ℝ) (x : Fin 6 → ℝ) :
    latticeCenter eps t (triIndex eps t x) =
      ![meshRound eps (x 0),meshRound eps (x 1),meshRound eps (cArgument eps t x),
        t,meshRound eps (eArgument eps t x),meshRound eps (x 5)] := by
  ext i
  fin_cases i <;> rfl

/-- The actual fixed-d cocycle retains both the tF and the c-coordinate shears. -/
theorem relative_at_fixed_d (eps t : ℝ) (x : Fin 6 → ℝ) (z : Fin 5 → ℤ)
    (ht : x 3 = t) :
    originalUpperRelativeFrame (latticeCenter eps t z) x =
      ![x 0-eps*z 0,x 1-eps*z 1,
        x 2-eps*z 2-eps*z 0*(x 4-eps*z 3-t*(x 5-eps*z 4))-eps*z 1*(x 5-eps*z 4),
        0,x 4-eps*z 3-t*(x 5-eps*z 4),x 5-eps*z 4] := by
  ext i
  fin_cases i <;>
    simp [originalUpperRelativeFrame,originalUpperAffineComp,originalUpperAffineInv,
      latticeCenter,ht] <;> ring

/-- Every point at the fixed original d-level is covered, independently of phase. -/
theorem rounded_relative_mem (eps t : ℝ) (x : Fin 6 → ℝ)
    (heps : 0 < eps) (ht : x 3 = t) :
    InRightDCube eps (originalUpperRelativeFrame (latticeCenter eps t (triIndex eps t x)) x) := by
  rw [relative_at_fixed_d eps t x _ ht]
  constructor
  · intro i
    fin_cases i
    · simpa [sliceCoord,triIndex,meshRound] using meshRound_residual eps (x 0) heps
    · simpa [sliceCoord,triIndex,meshRound] using meshRound_residual eps (x 1) heps
    · convert meshRound_residual eps (cArgument eps t x) heps using 1 <;>
        simp [sliceCoord,triIndex,cArgument,eArgument,meshRound] <;>
        ring_nf <;> constructor <;> intro h <;> linarith only [h]
    · convert meshRound_residual eps (eArgument eps t x) heps using 1 <;>
        simp [sliceCoord,triIndex,eArgument,meshRound] <;>
        ring_nf <;> constructor <;> intro h <;> linarith only [h]
    · simpa [sliceCoord,triIndex,meshRound] using meshRound_residual eps (x 5) heps
  · rfl

private theorem rounded_bound (x w K eps : ℝ)
    (hw : 1 ≤ w) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hx : |x| ≤ K*w) : |meshRound eps x| ≤ (K+1)*w := by
  calc
    _ ≤ |x|+eps := abs_meshRound_le eps x heps
    _ ≤ K*w+w := add_le_add hx (heps1.trans hw)
    _ = _ := by ring

/-- The rounded five-coordinate lattice labels stay in a fixed enlargement of
the exact I1523 box. The full box condition derives the bound on the fixed level. -/
theorem rounded_center_bound (H U W K eps t : ℝ) (x : Fin 6 → ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hx : OriginalDGaugeBox.BoxBound x K H U W) (ht : x 3 = t) :
    ∀ i : Fin 5, |eps * (triIndex eps t x i : ℝ)| ≤
      (3*K+3)*sliceWeight H U W i := by
  have hH0 : 0 ≤ H := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hHU : 1 ≤ H*U := one_le_mul_of_one_le_of_one_le hH hU
  have hHW : 1 ≤ H*W := one_le_mul_of_one_le_of_one_le hH hW
  have hHUW : 1 ≤ H*U*W := one_le_mul_of_one_le_of_one_le hHU hW
  have hU_HUW : U ≤ H*U*W := by
    calc
      U ≤ H*U := le_mul_of_one_le_left hU0 hH
      _ ≤ H*U*W := le_mul_of_one_le_right (mul_nonneg hH0 hU0) hW
  have hHU_HUW : H*U ≤ H*U*W := le_mul_of_one_le_right (mul_nonneg hH0 hU0) hW
  have hH_HW : H ≤ H*W := le_mul_of_one_le_right hH0 hW
  have hx0 := hx 0
  have hx1 := hx 1
  have hx2 := hx 2
  have hx3 := hx 3
  have hx4 := hx 4
  have hx5 := hx 5
  change |x 0| ≤ K*U at hx0
  change |x 1| ≤ K*(H*U) at hx1
  change |x 2| ≤ K*(H*U*W) at hx2
  change |x 3| ≤ K*H at hx3
  change |x 4| ≤ K*(H*W) at hx4
  change |x 5| ≤ K*W at hx5
  have hdt : |t| ≤ K*H := by simpa only [ht] using hx3
  have ha := rounded_bound (x 0) U K eps hU heps heps1 hx0
  have hb := rounded_bound (x 1) (H*U) K eps hHU heps heps1 hx1
  have hf := rounded_bound (x 5) W K eps hW heps heps1 hx5
  have hF : |x 5-meshRound eps (x 5)| ≤ eps := by
    rw [abs_of_nonneg (meshRound_residual eps (x 5) heps).1]
    exact (meshRound_residual eps (x 5) heps).2.le
  have hE : |eArgument eps t x-meshRound eps (eArgument eps t x)| ≤ eps := by
    rw [abs_of_nonneg (meshRound_residual eps (eArgument eps t x) heps).1]
    exact (meshRound_residual eps (eArgument eps t x) heps).2.le
  have htF : |t*(x 5-meshRound eps (x 5))| ≤ K*(H*W) := by
    calc
      _ = |t| * |x 5-meshRound eps (x 5)| := abs_mul _ _
      _ ≤ (K*H)*1 := mul_le_mul hdt (hF.trans heps1) (abs_nonneg _) (mul_nonneg hK0 hH0)
      _ ≤ K*(H*W) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hH_HW hK0
  have he : |meshRound eps (eArgument eps t x)| ≤ (2*K+1)*(H*W) := by
    calc
      _ ≤ |eArgument eps t x|+eps := abs_meshRound_le eps _ heps
      _ ≤ (|x 4|+|t*(x 5-meshRound eps (x 5))|)+eps :=
        add_le_add_right (abs_sub _ _) _
      _ ≤ (K*(H*W)+K*(H*W))+H*W :=
        add_le_add (add_le_add hx4 htF) (heps1.trans hHW)
      _ = _ := by ring
  have haE : |meshRound eps (x 0)*(eArgument eps t x-meshRound eps (eArgument eps t x))| ≤
      (K+1)*(H*U*W) := by
    calc
      _ = |meshRound eps (x 0)| * |eArgument eps t x-meshRound eps (eArgument eps t x)| := abs_mul _ _
      _ ≤ ((K+1)*U)*1 := mul_le_mul ha (hE.trans heps1) (abs_nonneg _) (by positivity)
      _ ≤ (K+1)*(H*U*W) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hU_HUW (by linarith : 0 ≤ K+1)
  have hbF : |meshRound eps (x 1)*(x 5-meshRound eps (x 5))| ≤ (K+1)*(H*U*W) := by
    calc
      _ = |meshRound eps (x 1)| * |x 5-meshRound eps (x 5)| := abs_mul _ _
      _ ≤ ((K+1)*(H*U))*1 := mul_le_mul hb (hF.trans heps1) (abs_nonneg _) (by positivity)
      _ ≤ (K+1)*(H*U*W) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hHU_HUW (by linarith : 0 ≤ K+1)
  have hc : |meshRound eps (cArgument eps t x)| ≤ (3*K+3)*(H*U*W) := by
    calc
      _ ≤ |cArgument eps t x|+eps := abs_meshRound_le eps _ heps
      _ ≤ (|x 2|+|meshRound eps (x 0)*(eArgument eps t x-meshRound eps (eArgument eps t x))|+
          |meshRound eps (x 1)*(x 5-meshRound eps (x 5))|)+eps :=
        add_le_add_right ((abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)) _
      _ ≤ (K*(H*U*W)+(K+1)*(H*U*W)+(K+1)*(H*U*W))+H*U*W :=
        add_le_add (add_le_add (add_le_add hx2 haE) hbF) (heps1.trans hHUW)
      _ = _ := by ring
  intro i
  fin_cases i
  · change |meshRound eps (x 0)| ≤ (3*K+3)*U
    exact ha.trans (mul_le_mul_of_nonneg_right (by linarith : K+1 ≤ 3*K+3) hU0)
  · change |meshRound eps (x 1)| ≤ (3*K+3)*(H*U)
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith : K+1 ≤ 3*K+3) (mul_nonneg hH0 hU0))
  · exact hc
  · change |meshRound eps (eArgument eps t x)| ≤ (3*K+3)*(H*W)
    exact he.trans (mul_le_mul_of_nonneg_right (by linarith : 2*K+1 ≤ 3*K+3) (mul_nonneg hH0 hW0))
  · change |meshRound eps (x 5)| ≤ (3*K+3)*W
    exact hf.trans (mul_le_mul_of_nonneg_right (by linarith : K+1 ≤ 3*K+3) hW0)

end PaperI.FixedDSliceRounding
