import PaperILean.AffineJetDerivatives
import PaperILean.OriginalGaussFrozenThird

/-! I848/I1293: the complete original coefficient vector in the literal
upper-affine frame. The coefficient space discards only the constant, so
normal derivative equivariance is asserted only at positive order. -/
noncomputable section
namespace PaperI
open Filter
open scoped Topology

def originalUpperLinearMatrix (g : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,g 0,g 1;0,1,g 3;0,0,1]

def originalUpperCoefficientPullback {k : ℕ} (F : CoefficientSpace k)
    (g : Fin 6 → ℝ) : CoefficientSpace k :=
  affineCoefficientMap k ![g 2,g 4,g 5] (originalUpperLinearMatrix g) F

theorem originalUpperAffineEval_eq_affinePoint (g : Fin 6 → ℝ) (x : PhysicalSpace) :
    originalUpperAffineEval g x = affinePoint ![g 2,g 4,g 5] (originalUpperLinearMatrix g) x := by
  ext i
  fin_cases i <;> simp [originalUpperAffineEval,affinePoint,originalUpperLinearMatrix,
    Matrix.mulVec, dotProduct,Fin.sum_univ_succ] <;> ring

theorem originalUpperLinearMatrix_normal (g : Fin 6 → ℝ) :
    frameLinearMap (originalUpperLinearMatrix g) (Pi.single (0 : Fin 3) (1 : ℝ)) =
      Pi.single (0 : Fin 3) (1 : ℝ) := by
  rw [frameLinearMap_apply,originalNormal_x_basis]
  ext i
  fin_cases i <;> simp [originalUpperLinearMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem originalUpperCoefficientPullback_phase {k : ℕ} (F : CoefficientSpace k)
    (g : Fin 6 → ℝ) (x : PhysicalSpace) :
    phase (originalUpperCoefficientPullback F g) x =
      phase F (originalUpperAffineEval g x)-phase F ![g 2,g 4,g 5] := by
  rw [originalUpperCoefficientPullback,phase_affineCoefficientMap,← originalUpperAffineEval_eq_affinePoint]

theorem originalUpperCoefficientPullback_normal {k : ℕ} (F : CoefficientSpace k)
    (g : Fin 6 → ℝ) (n : ℕ) (hn : 1 ≤ n) (x : PhysicalSpace) :
    originalNormalPhase (originalUpperCoefficientPullback F g) n x =
      originalNormalPhase F n (originalUpperAffineEval g x) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  unfold originalNormalPhase originalUpperCoefficientPullback
  rw [iteratedFDeriv_phase_affine_positive,← originalUpperAffineEval_eq_affinePoint]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,originalUpperLinearMatrix_normal]

theorem originalUpperCoefficientPullback_graph_root {k : ℕ} (F : CoefficientSpace k)
    (g : Fin 6 → ℝ) (n : ℕ) (hn : 1 ≤ n) (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) :
    originalNormalPhase (originalUpperCoefficientPullback F g) n
      ![originalGaussGraphPullback g c v,v 0,v 1] =
    originalNormalPhase F n
      ![c (originalGaussGraphBaseChange g v),
        originalGaussGraphBaseChange g v 0,originalGaussGraphBaseChange g v 1] := by
  rw [originalUpperCoefficientPullback_normal F g n hn,originalGaussGraphPullback_point]

theorem originalUpperCoefficientPullback_graph_root_germ {k : ℕ} (F : CoefficientSpace k)
    (g : Fin 6 → ℝ) (n : ℕ) (hn : 1 ≤ n) (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hroot : ∀ᶠ w in 𝓝 (originalGaussGraphBaseChange g v),
      originalNormalPhase F n ![c w,w 0,w 1]=0) :
    ∀ᶠ w in 𝓝 v, originalNormalPhase (originalUpperCoefficientPullback F g) n
      ![originalGaussGraphPullback g c w,w 0,w 1]=0 := by
  filter_upwards [(originalGaussGraphBaseChange_hasFDerivAt g v).continuousAt.eventually hroot] with w hw
  rw [originalUpperCoefficientPullback_graph_root F g n hn c w]
  exact hw

end PaperI
