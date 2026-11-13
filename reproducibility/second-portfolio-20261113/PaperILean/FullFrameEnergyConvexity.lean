import PaperILean.TensorExponentialSums
import PaperILean.FrameLogEnergyRecentering

/-! Assemble the full, unchanged energy on the exponential frame path at
Paper I248. Strictness uses lambda > 0 and H != 0 exactly where needed. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem convexOn_real_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ (fun t => ∑ i ∈ s, f i t) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i hi => (hf i hi).2 hx hy ha hb hab)

theorem convexOn_real_affine (m d : ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => m * t + d) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b _ _ hab
  simp only [smul_eq_mul]
  nlinarith [congrArg (fun z : ℝ => z * d) hab]

theorem strictConvexOn_real_const_mul (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (lam : ℝ) (hlam : 0 < lam) : StrictConvexOn ℝ Set.univ (fun t => lam * f t) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  calc
    lam * f (a • x + b • y) < lam * (a • f x + b • f y) :=
      mul_lt_mul_of_pos_left (hf.2 hx hy hxy ha hb hab) hlam
    _ = a • (lam * f x) + b • (lam * f y) := by simp only [smul_eq_mul]; ring

theorem matrixFullHSNorm_exp_convex {n : ℕ}
    (B H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    ConvexOn ℝ Set.univ (fun t : ℝ => (matrixFullHSNorm (B * NormedSpace.exp ℝ (t • H))) ^ 2) := by
  have heq : (fun t : ℝ => (matrixFullHSNorm (B * NormedSpace.exp ℝ (t • H))) ^ 2) =
      fun t => ∑ i : Fin n, weightedExponentialSum Finset.univ
        (fun j => ((B * (symmetricFrameEigenbasis H hH : Matrix (Fin n) (Fin n) ℝ)) i j) ^ 2)
        (fun j => 2 * symmetricFrameEigenvalues H hH j) t := by
    funext t
    exact matrixFullHSNorm_exp_eq_sum B H hH t
  rw [heq]
  exact convexOn_real_finset_sum _ _ (fun i _ =>
    weightedExponentialSum_convex _ _ _ (fun j _ => sq_nonneg _))

def frameNonlogEnergyCurve {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : PositiveFrame) (H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) : ℝ :=
  (matrixFullHSNorm (B.val * NormedSpace.exp ℝ (t • H))) ^ 2 +
    (∑ r ∈ Finset.Icc 2 k, (jetTensorHSNorm F c (B.val * NormedSpace.exp ℝ (t • H)) r) ^ 2) -
    2 * (Real.log B.val.det + t * Matrix.trace H)

def frameEnergyCurve {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) (B : PositiveFrame) (H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) : ℝ :=
  FrameEnergy F c lam (B.val * NormedSpace.exp ℝ (t • H))

theorem frameNonlogEnergyCurve_convex {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : PositiveFrame) (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    ConvexOn ℝ Set.univ (frameNonlogEnergyCurve F c B H) := by
  have hsum := convexOn_real_finset_sum (Finset.Icc 2 k)
    (fun r t => (jetTensorHSNorm F c (B.val * NormedSpace.exp ℝ (t • H)) r) ^ 2)
    (fun r _ => jetTensorHSNorm_exp_convex F c B.val H hH r)
  have h := ((matrixFullHSNorm_exp_convex B.val H hH).add hsum).add
    (convexOn_real_affine (-2 * Matrix.trace H) (-2 * Real.log B.val.det))
  convert h using 1
  funext t
  simp only [frameNonlogEnergyCurve, Pi.add_apply]
  ring

theorem frameEnergyCurve_eq_nonlog_add_log {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    frameEnergyCurve F c lam B H =
      fun t => frameNonlogEnergyCurve F c B H t + lam * frameLogEnergyCurve B H t := by
  funext t
  simp only [frameEnergyCurve, FrameEnergy, frameNonlogEnergyCurve, frameLogEnergyCurve,
    positiveFrame_log_det_exp B H hH t]

theorem frameEnergyCurve_zero_direction {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) :
    frameEnergyCurve F c lam B 0 = fun _ => FrameEnergy F c lam B.val := by
  funext t
  simp [frameEnergyCurve, NormedSpace.exp_zero]

theorem frameEnergyCurve_strictConvex {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (hne : H ≠ 0) :
    StrictConvexOn ℝ Set.univ (frameEnergyCurve F c lam B H) := by
  rw [frameEnergyCurve_eq_nonlog_add_log F c lam B H hH]
  exact (frameNonlogEnergyCurve_convex F c B H hH).add_strictConvexOn
    (strictConvexOn_real_const_mul _ (frameLogEnergyCurve_strictConvex B H hH hne) lam hlam)

theorem frameEnergyCurve_convex {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    ConvexOn ℝ Set.univ (frameEnergyCurve F c lam B H) := by
  by_cases hzero : H = 0
  · rw [hzero, frameEnergyCurve_zero_direction]
    exact convexOn_const _ convex_univ
  · exact (frameEnergyCurve_strictConvex F c lam hlam B H hH hzero).convexOn

end PaperI
