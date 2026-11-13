import PaperILean.TensorPairingDerivative
import PaperILean.FrameBalance

/-! I286-290: differentiate the actual frame first variation in the center.
The center direction is B*h with B fixed, and the frame curve is B*exp(sH).
The exact coefficient4 uses the explicitly assumed symmetry of H. No
minimality, genericity, nonzero direction or positivity of lambda is needed.
-/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def jetCenterFrameMixedTerm {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (h : PhysicalSpace)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) : ℝ :=
  tensorHSInner ((affineJetTensor F c B (r + 1)).curryLeft h)
    (tensorSlotAction H (affineJetTensor F c B r))

theorem jetCenterFrameMixedTerm_eq_zero_of_degree_le {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (h : PhysicalSpace)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) (hr : k ≤ r) :
    jetCenterFrameMixedTerm F c B h H r = 0 := by
  have hz := affineJetTensor_eq_zero_of_degree_lt F c B (r + 1) (by omega)
  simp [jetCenterFrameMixedTerm, hz, tensorHSInner, tensorCoordinates,
    ContinuousMultilinearMap.curryLeft_apply]

theorem jetCenterFrameMixedTerm_sum_truncate {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (h : PhysicalSpace)
    (H : Matrix (Fin 3) (Fin 3) ℝ) :
    (∑ r ∈ Finset.Icc 2 k, jetCenterFrameMixedTerm F c B h H r) =
      ∑ r ∈ Finset.Icc 2 (k - 1), jetCenterFrameMixedTerm F c B h H r := by
  symm
  apply Finset.sum_subset
  · intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  · intro r hr hnot
    have he : r = k := by
      simp only [Finset.mem_Icc] at hr hnot
      omega
    subst r
    exact jetCenterFrameMixedTerm_eq_zero_of_degree_le F c B h H k le_rfl

theorem hasDerivAt_jet_frame_firstVariation_center_zero {k : ℕ} (F : CoefficientSpace k)
    (r : ℕ) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (h : PhysicalSpace) (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    HasDerivAt (fun t : ℝ => 2 * tensorHSInner
      (affineJetTensor F (c + t • (B *ᵥ h)) B r)
      (tensorSlotAction H (affineJetTensor F (c + t • (B *ᵥ h)) B r)))
      (4 * jetCenterFrameMixedTerm F c B h H r) 0 := by
  have hd := hasDerivAt_tensorHSInner_slot_self
    (hasDerivAt_affineJetTensor_center_zero F r c B h) H hH
  simpa only [zero_smul, add_zero, jetCenterFrameMixedTerm, ← mul_assoc,
    show (2 : ℝ) * 2 = 4 by norm_num] using hd.const_mul 2

theorem hasDerivAt_frameEnergyCurve_tensor {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    HasDerivAt (frameEnergyCurve F c lam B H)
      (2 * Matrix.trace (B.valᵀ * B.val * H) +
        (∑ r ∈ Finset.Icc 2 k, 2 * tensorHSInner (affineJetTensor F c B.val r)
          (tensorSlotAction H (affineJetTensor F c B.val r))) -
        2 * Matrix.trace H + lam * (4 * Matrix.trace (CFC.log (B.valᵀ * B.val) * H))) 0 := by
  have ht := HasDerivAt.sum (u := Finset.Icc 2 k) (fun r _ =>
    hasDerivAt_jetTensorHSNorm_sq_frame_zero F c B.val H hH (r := r))
  have hd := ((hasDerivAt_const (0 : ℝ) (Real.log B.val.det)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (Matrix.trace H))).const_mul 2
  have hh := (((hasDerivAt_matrixFullHSNorm_sq_frame_zero B.val H).add ht).sub hd).add
    ((hasDerivAt_frameLogEnergyCurve_zero B H hH).const_mul lam)
  rw [frameEnergyCurve_eq_nonlog_add_log F c lam B H hH]
  simpa only [frameNonlogEnergyCurve, zero_add, one_mul] using hh

theorem hasDerivAt_frameEnergyCurve_center_firstVariation {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) (h : PhysicalSpace)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    HasDerivAt (fun t : ℝ => deriv (frameEnergyCurve F (c + t • (B.val *ᵥ h)) lam B H) 0)
      (4 * ∑ r ∈ Finset.Icc 2 (k - 1), jetCenterFrameMixedTerm F c B.val h H r) 0 := by
  have he : (fun t : ℝ => deriv (frameEnergyCurve F (c + t • (B.val *ᵥ h)) lam B H) 0) =
      fun t => 2 * Matrix.trace (B.valᵀ * B.val * H) +
        (∑ r ∈ Finset.Icc 2 k, 2 * tensorHSInner (affineJetTensor F (c + t • (B.val *ᵥ h)) B.val r)
          (tensorSlotAction H (affineJetTensor F (c + t • (B.val *ᵥ h)) B.val r))) -
        2 * Matrix.trace H + lam * (4 * Matrix.trace (CFC.log (B.valᵀ * B.val) * H)) := by
    funext t
    exact (hasDerivAt_frameEnergyCurve_tensor F _ lam B H hH).deriv
  rw [he]
  have hs := HasDerivAt.sum (u := Finset.Icc 2 k) (fun r _ =>
    hasDerivAt_jet_frame_firstVariation_center_zero F r c B.val h H hH)
  have hd := (((hasDerivAt_const (0 : ℝ) (2 * Matrix.trace (B.valᵀ * B.val * H))).add hs).sub
    (hasDerivAt_const (0 : ℝ) (2 * Matrix.trace H))).add
    (hasDerivAt_const (0 : ℝ) (lam * (4 * Matrix.trace (CFC.log (B.valᵀ * B.val) * H))))
  simpa only [zero_add, sub_zero, add_zero, ← Finset.mul_sum,
    jetCenterFrameMixedTerm_sum_truncate] using hd

theorem frameEnergy_center_frame_mixed_derivative {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) (h : PhysicalSpace)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    deriv (fun t : ℝ => deriv (fun s : ℝ =>
      FrameEnergy F (c + t • (B.val *ᵥ h)) lam (B.val * NormedSpace.exp ℝ (s • H))) 0) 0 =
      4 * ∑ r ∈ Finset.Icc 2 (k - 1),
        tensorHSInner ((affineJetTensor F c B.val (r + 1)).curryLeft h)
          (tensorSlotAction H (affineJetTensor F c B.val r)) :=
  (hasDerivAt_frameEnergyCurve_center_firstVariation F c lam B h H hH).deriv

end PaperI
