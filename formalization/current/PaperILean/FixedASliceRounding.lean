import PaperILean.FixedFSliceRounding
import PaperILean.FixedABoxComparisons

/-! Triangular rounding for the original fixed-a sampling nets in cases15/16.
The source is the entire stated original box at a prescribed original a-level.
No target net, phase witness or selected sample is assumed. -/
noncomputable section
namespace PaperI.FixedASliceRounding
open FixedFSliceRounding

def sliceCoord : Fin 5 → Fin 6 := ![1,2,3,4,5]

def sliceWeight (H U W : ℝ) : Fin 5 → ℝ :=
  ![H*U,H*(H+U*W),U,H+U*W,W]

def bArgument (eps t : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  x 1 - t * (x 3 - meshRound eps (x 3))

def eArgument (eps : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  x 4 - meshRound eps (x 3) * (x 5 - meshRound eps (x 5))

def cArgument (eps t : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  x 2 - t * (eArgument eps x - meshRound eps (eArgument eps x)) -
    meshRound eps (bArgument eps t x) * (x 5 - meshRound eps (x 5))

def triIndex (eps t : ℝ) (x : Fin 6 → ℝ) : Fin 5 → ℤ :=
  ![⌊bArgument eps t x / eps⌋,⌊cArgument eps t x / eps⌋,
    ⌊x 3 / eps⌋,⌊eArgument eps x / eps⌋,⌊x 5 / eps⌋]

def latticeCenter (eps t : ℝ) (z : Fin 5 → ℤ) : Fin 6 → ℝ :=
  ![t,eps*z 0,eps*z 1,eps*z 2,eps*z 3,eps*z 4]

def InRightACube (eps : ℝ) (r : Fin 6 → ℝ) : Prop :=
  (∀ i : Fin 5, 0 ≤ r (sliceCoord i) ∧ r (sliceCoord i) < eps) ∧ r 0 = 0

@[simp] theorem latticeCenter_fixed_a (eps t : ℝ) (z : Fin 5 → ℤ) :
    latticeCenter eps t z 0 = t := rfl

/-- The exact original right-relative factor keeps the tD, d0F, tE and b0F terms. -/
theorem relative_at_fixed_a (eps t : ℝ) (x : Fin 6 → ℝ) (z : Fin 5 → ℤ)
    (ht : x 0 = t) :
    originalUpperRelativeFrame (latticeCenter eps t z) x =
      ![0,x 1-eps*z 0-t*(x 3-eps*z 2),
        x 2-eps*z 1-t*(x 4-eps*z 3-eps*z 2*(x 5-eps*z 4))-eps*z 0*(x 5-eps*z 4),
        x 3-eps*z 2,x 4-eps*z 3-eps*z 2*(x 5-eps*z 4),x 5-eps*z 4] := by
  ext i
  fin_cases i <;>
    simp [originalUpperRelativeFrame,originalUpperAffineComp,originalUpperAffineInv,
      latticeCenter,ht] <;> ring

/-- Every point at the fixed original a-level is covered by its triangular rounded center. -/
theorem rounded_relative_mem (eps t : ℝ) (x : Fin 6 → ℝ)
    (heps : 0 < eps) (ht : x 0 = t) :
    InRightACube eps (originalUpperRelativeFrame (latticeCenter eps t (triIndex eps t x)) x) := by
  rw [relative_at_fixed_a eps t x _ ht]
  constructor
  · intro i
    fin_cases i
    · convert meshRound_residual eps (bArgument eps t x) heps using 1 <;>
        simp [sliceCoord,triIndex,bArgument,meshRound] <;>
        ring_nf <;> constructor <;> intro h <;> linarith only [h]
    · convert meshRound_residual eps (cArgument eps t x) heps using 1 <;>
        simp [sliceCoord,triIndex,cArgument,bArgument,eArgument,meshRound] <;>
        ring_nf <;> constructor <;> intro h <;> linarith only [h]
    · simpa [sliceCoord,triIndex,meshRound] using meshRound_residual eps (x 3) heps
    · convert meshRound_residual eps (eArgument eps x) heps using 1 <;>
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

/-- Every triangular index belongs to one fixed polynomial enlargement of the
five-coordinate catalog. The fixed level bound is derived from the source box. -/
theorem rounded_center_bound (H U W K eps t : ℝ) (x : Fin 6 → ℝ)
    (hH : 1 ≤ H) (hU : 1 ≤ U) (hW : 1 ≤ W) (hK : 1 ≤ K)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hx : FixedABoxComparisons.BoxBound x K H U W) (ht : x 0 = t) :
    ∀ i : Fin 5, |eps * (triIndex eps t x i : ℝ)| ≤
      (6*K)*sliceWeight H U W i := by
  have hH0 : 0 ≤ H := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hHU : 1 ≤ H*U := one_le_mul_of_one_le_of_one_le hH hU
  have hUW : 1 ≤ U*W := one_le_mul_of_one_le_of_one_le hU hW
  have hE : 1 ≤ H+U*W := by linarith
  have hC : 1 ≤ H*(H+U*W) := one_le_mul_of_one_le_of_one_le hH hE
  have hH_HU : H ≤ H*U := le_mul_of_one_le_right hH0 hU
  have hU_E : U ≤ H+U*W := by
    have := le_mul_of_one_le_right hU0 hW
    linarith
  have hH_C : H ≤ H*(H+U*W) := le_mul_of_one_le_right hH0 hE
  have hHU_C : H*U ≤ H*(H+U*W) := mul_le_mul_of_nonneg_left hU_E hH0
  have hx0 := hx 0
  have hx1 := hx 1
  have hx2 := hx 2
  have hx3 := hx 3
  have hx4 := hx 4
  have hx5 := hx 5
  change |x 0| ≤ K*H at hx0
  change |x 1| ≤ K*(H*U) at hx1
  change |x 2| ≤ K*(H*(H+U*W)) at hx2
  change |x 3| ≤ K*U at hx3
  change |x 4| ≤ K*(H+U*W) at hx4
  change |x 5| ≤ K*W at hx5
  have hat : |t| ≤ K*H := by simpa only [ht] using hx0
  have hd := rounded_bound (x 3) U K eps hU heps heps1 hx3
  have hf := rounded_bound (x 5) W K eps hW heps heps1 hx5
  have hD : |x 3-meshRound eps (x 3)| ≤ eps := by
    rw [abs_of_nonneg (meshRound_residual eps (x 3) heps).1]
    exact (meshRound_residual eps (x 3) heps).2.le
  have hF : |x 5-meshRound eps (x 5)| ≤ eps := by
    rw [abs_of_nonneg (meshRound_residual eps (x 5) heps).1]
    exact (meshRound_residual eps (x 5) heps).2.le
  have hEr : |eArgument eps x-meshRound eps (eArgument eps x)| ≤ eps := by
    rw [abs_of_nonneg (meshRound_residual eps (eArgument eps x) heps).1]
    exact (meshRound_residual eps (eArgument eps x) heps).2.le
  have htD : |t*(x 3-meshRound eps (x 3))| ≤ K*(H*U) := by
    calc
      _ = |t| * |x 3-meshRound eps (x 3)| := abs_mul _ _
      _ ≤ (K*H)*1 := mul_le_mul hat (hD.trans heps1) (abs_nonneg _) (mul_nonneg hK0 hH0)
      _ ≤ K*(H*U) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hH_HU hK0
  have hb : |meshRound eps (bArgument eps t x)| ≤ (2*K+1)*(H*U) := by
    calc
      _ ≤ |bArgument eps t x|+eps := abs_meshRound_le eps _ heps
      _ ≤ (|x 1|+|t*(x 3-meshRound eps (x 3))|)+eps := add_le_add_right (abs_sub _ _) _
      _ ≤ (K*(H*U)+K*(H*U))+H*U := add_le_add (add_le_add hx1 htD) (heps1.trans hHU)
      _ = _ := by ring
  have hdF : |meshRound eps (x 3)*(x 5-meshRound eps (x 5))| ≤ (K+1)*(H+U*W) := by
    calc
      _ = |meshRound eps (x 3)| * |x 5-meshRound eps (x 5)| := abs_mul _ _
      _ ≤ ((K+1)*U)*1 := mul_le_mul hd (hF.trans heps1) (abs_nonneg _) (by positivity)
      _ ≤ (K+1)*(H+U*W) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hU_E (by linarith : 0 ≤ K+1)
  have he : |meshRound eps (eArgument eps x)| ≤ (2*K+2)*(H+U*W) := by
    calc
      _ ≤ |eArgument eps x|+eps := abs_meshRound_le eps _ heps
      _ ≤ (|x 4|+|meshRound eps (x 3)*(x 5-meshRound eps (x 5))|)+eps :=
        add_le_add_right (abs_sub _ _) _
      _ ≤ (K*(H+U*W)+(K+1)*(H+U*W))+(H+U*W) :=
        add_le_add (add_le_add hx4 hdF) (heps1.trans hE)
      _ = _ := by ring
  have htE : |t*(eArgument eps x-meshRound eps (eArgument eps x))| ≤ K*(H*(H+U*W)) := by
    calc
      _ = |t| * |eArgument eps x-meshRound eps (eArgument eps x)| := abs_mul _ _
      _ ≤ (K*H)*1 := mul_le_mul hat (hEr.trans heps1) (abs_nonneg _) (mul_nonneg hK0 hH0)
      _ ≤ K*(H*(H+U*W)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hH_C hK0
  have hbF : |meshRound eps (bArgument eps t x)*(x 5-meshRound eps (x 5))| ≤
      (2*K+1)*(H*(H+U*W)) := by
    calc
      _ = |meshRound eps (bArgument eps t x)| * |x 5-meshRound eps (x 5)| := abs_mul _ _
      _ ≤ ((2*K+1)*(H*U))*1 := mul_le_mul hb (hF.trans heps1) (abs_nonneg _) (by positivity)
      _ ≤ (2*K+1)*(H*(H+U*W)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hHU_C (by linarith : 0 ≤ 2*K+1)
  have hc : |meshRound eps (cArgument eps t x)| ≤ (4*K+2)*(H*(H+U*W)) := by
    calc
      _ ≤ |cArgument eps t x|+eps := abs_meshRound_le eps _ heps
      _ ≤ (|x 2|+|t*(eArgument eps x-meshRound eps (eArgument eps x))|+
          |meshRound eps (bArgument eps t x)*(x 5-meshRound eps (x 5))|)+eps :=
        add_le_add_right ((abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)) _
      _ ≤ (K*(H*(H+U*W))+K*(H*(H+U*W))+(2*K+1)*(H*(H+U*W)))+H*(H+U*W) :=
        add_le_add (add_le_add (add_le_add hx2 htE) hbF) (heps1.trans hC)
      _ = _ := by ring
  intro i
  fin_cases i
  · change |meshRound eps (bArgument eps t x)| ≤ (6*K)*(H*U)
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith : 2*K+1 ≤ 6*K) (by positivity))
  · change |meshRound eps (cArgument eps t x)| ≤ (6*K)*(H*(H+U*W))
    exact hc.trans (mul_le_mul_of_nonneg_right (by linarith : 4*K+2 ≤ 6*K) (by positivity))
  · change |meshRound eps (x 3)| ≤ (6*K)*U
    exact hd.trans (mul_le_mul_of_nonneg_right (by linarith : K+1 ≤ 6*K) hU0)
  · change |meshRound eps (eArgument eps x)| ≤ (6*K)*(H+U*W)
    exact he.trans (mul_le_mul_of_nonneg_right (by linarith : 2*K+2 ≤ 6*K) (by positivity))
  · change |meshRound eps (x 5)| ≤ (6*K)*W
    exact hf.trans (mul_le_mul_of_nonneg_right (by linarith : K+1 ≤ 6*K) hW0)

end PaperI.FixedASliceRounding
