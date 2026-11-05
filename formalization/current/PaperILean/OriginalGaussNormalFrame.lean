import PaperILean.OriginalGaussFixedFrameArea
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! I1293/I1309: the manuscript's normalized Gauss frame and graph covariance.
The branch values c,Y,q0,d are supplied; this does not construct admissible
root charts or prove the original label's initial comparison with a root frame.
-/
noncomputable section
namespace PaperI
open Set Metric MeasureTheory

def originalGaussNormalFrame (p z c Y q0 d : ℝ) : Fin 6 → ℝ :=
  ![p,q0+d*p,c,d,Y,z]

theorem originalGaussNormalFrame_eval (p z c Y q0 d : ℝ) (x : Fin 3 → ℝ) :
    originalUpperAffineEval (originalGaussNormalFrame p z c Y q0 d) x =
      ![x 0+c+p*x 1+(q0+d*p)*x 2,Y+x 1+d*x 2,z+x 2] := by
  funext i
  fin_cases i <;> simp [originalUpperAffineEval,originalGaussNormalFrame] <;> ring

theorem originalGaussNormalFrame_projection (p z c Y q0 d : ℝ) :
    originalGaussProjection (originalGaussNormalFrame p z c Y q0 d)=
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![p,z] := rfl

theorem originalGaussNormalFrame_fixed_frame_covariance
    (g : Fin 6 → ℝ) (p z c Y q0 d : ℝ) :
    originalUpperAffineComp (originalUpperAffineInv g)
      (originalGaussNormalFrame p z c Y q0 d)=
      originalGaussNormalFrame (p-g 0) (z-g 5)
        (c-g 0*(Y-g 3*(z-g 5)-g 4)-g 1*(z-g 5)-g 2)
        (Y-g 3*(z-g 5)-g 4) (q0+g 3*p-g 1) (d-g 3) := by
  funext i
  fin_cases i <;>
    simp [originalUpperAffineComp,originalUpperAffineInv,originalGaussNormalFrame] <;> ring

def originalGaussGraphBaseChange (g : Fin 6 → ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![v 0+g 3*v 1+g 4,v 1+g 5]

def originalGaussGraphPullback (g : Fin 6 → ℝ) (c : (Fin 2 → ℝ) → ℝ)
    (v : Fin 2 → ℝ) : ℝ :=
  c (originalGaussGraphBaseChange g v)-g 0*v 0-g 1*v 1-g 2

theorem originalGaussGraphPullback_point (g : Fin 6 → ℝ)
    (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) :
    originalUpperAffineEval g ![originalGaussGraphPullback g c v,v 0,v 1]=
      ![c (originalGaussGraphBaseChange g v),
        originalGaussGraphBaseChange g v 0,originalGaussGraphBaseChange g v 1] := by
  funext i
  fin_cases i <;>
    simp [originalUpperAffineEval,originalGaussGraphPullback,originalGaussGraphBaseChange] <;> ring

theorem originalGaussGraphPullback_zero_iff (g : Fin 6 → ℝ)
    (c : (Fin 2 → ℝ) → ℝ) (G : (Fin 3 → ℝ) → ℝ) (v : Fin 2 → ℝ) :
    G (originalUpperAffineEval g ![originalGaussGraphPullback g c v,v 0,v 1])=0 ↔
      G ![c (originalGaussGraphBaseChange g v),
        originalGaussGraphBaseChange g v 0,originalGaussGraphBaseChange g v 1]=0 := by
  rw [originalGaussGraphPullback_point]

theorem originalGaussGraphPullback_first_derivatives
    (g : Fin 6 → ℝ) (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ)
    (dc : (Fin 2 → ℝ) →L[ℝ] ℝ)
    (hc : HasFDerivAt c dc (originalGaussGraphBaseChange g ![y,z])) :
    HasDerivAt (fun t => originalGaussGraphPullback g c ![t,z])
        (dc ![1,0]-g 0) y ∧
      HasDerivAt (fun t => originalGaussGraphPullback g c ![y,t])
        (g 3*dc ![1,0]+dc ![0,1]-g 1) z := by
  have hy : HasDerivAt (fun t : ℝ => originalGaussGraphBaseChange g ![t,z]) ![1,0] y := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [originalGaussGraphBaseChange] using
        (((hasDerivAt_id y).add_const (g 3*z)).add_const (g 4))
    · simpa [originalGaussGraphBaseChange] using hasDerivAt_const y (z+g 5)
  have hz : HasDerivAt (fun t : ℝ => originalGaussGraphBaseChange g ![y,t]) ![g 3,1] z := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [originalGaussGraphBaseChange] using
        (((hasDerivAt_id z).const_mul (g 3)).const_add y).add_const (g 4)
    · simpa [originalGaussGraphBaseChange] using (hasDerivAt_id z).add_const (g 5)
  have hd : dc ![g 3,1]=g 3*dc ![1,0]+dc ![0,1] := by
    have heq : (![g 3,1] : Fin 2 → ℝ)=g 3 • ![1,0]+![0,1] := by
      funext i
      fin_cases i <;> simp
    rw [heq,map_add,map_smul]
    rfl
  constructor
  · simpa [originalGaussGraphPullback] using
      (((hc.comp_hasDerivAt y hy).sub ((hasDerivAt_id y).const_mul (g 0))).sub_const (g 1*z)).sub_const (g 2)
  · simpa [originalGaussGraphPullback,hd] using
      (((hc.comp_hasDerivAt z hz).sub_const (g 0*y)).sub ((hasDerivAt_id z).const_mul (g 1))).sub_const (g 2)

end PaperI
