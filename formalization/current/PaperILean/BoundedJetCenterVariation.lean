import PaperILean.TensorContractionBounds

/-! Uniform higher-jet variation on the manuscript's bounded jet window.
The left side is the HS norm of each tensor difference. The displacement is
measured in normalized Euclidean coordinates. No inverse matrix is needed.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

def affineJetTensor {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) : TensorSpace r :=
  (iteratedFDeriv ℝ r (phase F) c).compContinuousLinearMap (fun _ => frameLinearMap B)

theorem affineJetTensor_apply {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) (v : Fin r → PhysicalSpace) :
    affineJetTensor F c B r v = iteratedFDeriv ℝ r (phase F) c (fun j => B *ᵥ v j) := by
  simp [affineJetTensor, frameLinearMap_apply]

theorem tensorHSNorm_affineJetTensor {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) :
    tensorHSNorm (affineJetTensor F c B r) = jetTensorHSNorm F c B r := by
  unfold tensorHSNorm coordinateL2Norm tensorCoordinates jetTensorHSNorm jetTensorComponent
  simp only [affineJetTensor_apply]

theorem prependDirections_frame (m r : ℕ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (h : PhysicalSpace) (v : Fin r → PhysicalSpace) :
    (fun j => B *ᵥ prependDirections m r (fun _ => h) v j) =
      prependDirections m r (fun _ => B *ᵥ h) (fun j => B *ᵥ v j) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext j
    refine Fin.cases ?_ (fun l => ?_) j
    · rfl
    · exact congrFun ih l

theorem affineJetTensor_center_transport {k : ℕ} (F : CoefficientSpace k)
    (r : ℕ) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (h : PhysicalSpace) :
    affineJetTensor F (c + B *ᵥ h) B r =
      ∑ m ∈ Finset.range (k - r + 1), (m.factorial : ℝ)⁻¹ •
        tensorContractRepeated m r (affineJetTensor F c B (r + m)) h := by
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul, tensorContractRepeated_apply, affineJetTensor_apply, prependDirections_frame]
  exact affineJet_center_transport k F r c B h v

theorem affineJetTensor_center_difference {k : ℕ} (F : CoefficientSpace k)
    (r : ℕ) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (h : PhysicalSpace) :
    affineJetTensor F (c + B *ᵥ h) B r - affineJetTensor F c B r =
      ∑ m ∈ Finset.range (k - r), ((m + 1).factorial : ℝ)⁻¹ •
        tensorContractRepeated (m + 1) r (affineJetTensor F c B (r + (m + 1))) h := by
  rw [affineJetTensor_center_transport, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, Nat.add_zero,
    tensorContractRepeated, one_smul]
  abel

def jetTensorDifferenceHSNorm {k : ℕ} (F : CoefficientSpace k)
    (c c' : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) : ℝ :=
  tensorHSNorm (affineJetTensor F c' B r - affineJetTensor F c B r)

theorem jetTensorDifferenceHSNorm_eq_coordinates {k : ℕ} (F : CoefficientSpace k)
    (c c' : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) :
    jetTensorDifferenceHSNorm F c c' B r = Real.sqrt
      (∑ a : Fin r → Fin 3, (jetTensorComponent F c' B r a -
        jetTensorComponent F c B r a) ^ 2) := by
  simp [jetTensorDifferenceHSNorm, tensorHSNorm, coordinateL2Norm, tensorCoordinates,
    jetTensorComponent, affineJetTensor_apply]

theorem factorial_inv_nonneg (m : ℕ) : 0 ≤ (m.factorial : ℝ)⁻¹ := by positivity

theorem factorial_inv_le_one (m : ℕ) : (m.factorial : ℝ)⁻¹ ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)

theorem jetTensorDifferenceHSNorm_le_transport {k : ℕ} (F : CoefficientSpace k)
    (r : ℕ) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (h : PhysicalSpace) :
    jetTensorDifferenceHSNorm F c (c + B *ᵥ h) B r ≤
      ∑ m ∈ Finset.range (k - r), ((m + 1).factorial : ℝ)⁻¹ *
        (physicalEuclideanNorm h ^ (m + 1) * jetTensorHSNorm F c B (r + (m + 1))) := by
  unfold jetTensorDifferenceHSNorm
  rw [affineJetTensor_center_difference]
  apply (tensorHSNorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m _
  rw [tensorHSNorm_smul, abs_of_nonneg (factorial_inv_nonneg _)]
  have hc := tensorHSNorm_contractRepeated_le (m + 1) r
    (affineJetTensor F c B (r + (m + 1))) h
  rw [tensorHSNorm_affineJetTensor] at hc
  exact mul_le_mul_of_nonneg_left hc (factorial_inv_nonneg _)

theorem boundedJet_window_nonneg {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (M : ℝ)
    (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M) : 0 ≤ M :=
  (Finset.sum_nonneg (fun r _ => jetTensorHSNorm_nonneg F c B r)).trans hM

theorem jetTensorHSNorm_le_window {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (M : ℝ)
    (hM : ∑ s ∈ Finset.Icc 2 k, jetTensorHSNorm F c B s ≤ M)
    (r : ℕ) (hr : r ∈ Finset.Icc 2 k) : jetTensorHSNorm F c B r ≤ M :=
  (Finset.single_le_sum (fun s _ => jetTensorHSNorm_nonneg F c B s) hr).trans hM

theorem euclideanNorm_pow_succ_le (h : PhysicalSpace) (hh : physicalEuclideanNorm h ≤ 1)
    (m : ℕ) : physicalEuclideanNorm h ^ (m + 1) ≤ physicalEuclideanNorm h := by
  rw [pow_succ]
  have hp : physicalEuclideanNorm h ^ m ≤ 1 :=
    pow_le_one₀ (physicalEuclideanNorm_nonneg h) hh
  simpa using mul_le_mul_of_nonneg_right hp (physicalEuclideanNorm_nonneg h)

theorem boundedJet_center_variation_order {k : ℕ} (F : CoefficientSpace k)
    (r : ℕ) (hr : r ∈ Finset.Icc 2 k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (h : PhysicalSpace) (M : ℝ)
    (hM : ∑ s ∈ Finset.Icc 2 k, jetTensorHSNorm F c B s ≤ M)
    (hh : physicalEuclideanNorm h ≤ 1) :
    jetTensorDifferenceHSNorm F c (c + B *ᵥ h) B r ≤
      (k - r : ℕ) * (M * physicalEuclideanNorm h) := by
  apply (jetTensorDifferenceHSNorm_le_transport F r c B h).trans
  calc
    (∑ m ∈ Finset.range (k - r), ((m + 1).factorial : ℝ)⁻¹ *
      (physicalEuclideanNorm h ^ (m + 1) * jetTensorHSNorm F c B (r + (m + 1)))) ≤
        ∑ _m ∈ Finset.range (k - r), M * physicalEuclideanNorm h := by
      apply Finset.sum_le_sum
      intro m hm
      have hrs := Finset.mem_Icc.mp hr
      have hmk := Finset.mem_range.mp hm
      have hs : r + (m + 1) ∈ Finset.Icc 2 k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hb := jetTensorHSNorm_le_window F c B M hM _ hs
      have hval0 : 0 ≤ physicalEuclideanNorm h ^ (m + 1) *
          jetTensorHSNorm F c B (r + (m + 1)) := mul_nonneg
            (pow_nonneg (physicalEuclideanNorm_nonneg h) _) (jetTensorHSNorm_nonneg _ _ _ _)
      calc
        _ ≤ physicalEuclideanNorm h ^ (m + 1) * jetTensorHSNorm F c B (r + (m + 1)) :=
          by simpa using mul_le_mul_of_nonneg_right (factorial_inv_le_one _) hval0
        _ ≤ physicalEuclideanNorm h * M := mul_le_mul
          (euclideanNorm_pow_succ_le h hh m) hb (jetTensorHSNorm_nonneg _ _ _ _)
          (physicalEuclideanNorm_nonneg h)
        _ = M * physicalEuclideanNorm h := mul_comm _ _
    _ = _ := by simp

theorem boundedJet_center_variation_bound (k : ℕ) (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (h : PhysicalSpace) (M : ℝ)
    (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M)
    (hh : physicalEuclideanNorm h ≤ 1) :
    ∑ r ∈ Finset.Icc 2 k, jetTensorDifferenceHSNorm F c (c + B *ᵥ h) B r ≤
      (k : ℝ) ^ 2 * M * physicalEuclideanNorm h := by
  have hMh : 0 ≤ M * physicalEuclideanNorm h := mul_nonneg
    (boundedJet_window_nonneg F c B M hM) (physicalEuclideanNorm_nonneg h)
  calc
    _ ≤ ∑ _r ∈ Finset.Icc 2 k, (k : ℝ) * (M * physicalEuclideanNorm h) := by
      apply Finset.sum_le_sum
      intro r hr
      apply (boundedJet_center_variation_order F r hr c B h M hM hh).trans
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le k r) hMh
    _ = ((Finset.Icc 2 k).card : ℝ) * ((k : ℝ) * (M * physicalEuclideanNorm h)) := by
      simp
    _ ≤ (k : ℝ) * ((k : ℝ) * (M * physicalEuclideanNorm h)) := by
      have hcard : (Finset.Icc 2 k).card ≤ k := by rw [Nat.card_Icc]; omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (mul_nonneg (Nat.cast_nonneg k) hMh)
    _ = _ := by ring

theorem boundedJet_center_variation (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (F : CoefficientSpace k) (c : PhysicalSpace)
      (B : Matrix (Fin 3) (Fin 3) ℝ) (h : PhysicalSpace),
      (∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M) →
      physicalEuclideanNorm h ≤ 1 →
      ∑ r ∈ Finset.Icc 2 k, jetTensorDifferenceHSNorm F c (c + B *ᵥ h) B r ≤
        C * M * physicalEuclideanNorm h := by
  refine ⟨(k : ℝ) ^ 2, sq_nonneg _, ?_⟩
  intro M F c B h hM hh
  exact boundedJet_center_variation_bound k F c B h M hM hh

end PaperI
