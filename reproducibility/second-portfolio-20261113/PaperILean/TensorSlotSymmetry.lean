import PaperILean.TensorFrameVariations

/-! Permutation symmetry accounts for the exact tensor order in I250-254.
The Gram matrix is the actual first-slot contraction Gram, not a definition
chosen to make the variation identity tautological. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem tensorHSInner_sum_right {r : ℕ} {ι : Type*} (T : TensorSpace r)
    (s : Finset ι) (S : ι → TensorSpace r) :
    tensorHSInner T (∑ i ∈ s, S i) = ∑ i ∈ s, tensorHSInner T (S i) := by
  simp only [tensorHSInner, tensorCoordinates, ContinuousMultilinearMap.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem tensorHSInner_permute {r : ℕ} (T S : TensorSpace r) (σ : Equiv.Perm (Fin r)) :
    tensorHSInner (T.domDomCongr σ) (S.domDomCongr σ) = tensorHSInner T S := by
  have he := (Equiv.arrowCongr σ.symm (Equiv.refl (Fin 3))).sum_comp
    (fun a : Fin r → Fin 3 => tensorCoordinates T a * tensorCoordinates S a)
  simpa only [tensorHSInner, tensorCoordinates, ContinuousMultilinearMap.domDomCongr_apply,
    Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.refl_apply, Function.comp_def] using he

theorem tensorOneSlotAction_permute {r : ℕ} (T : TensorSpace r)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin r) (σ : Equiv.Perm (Fin r)) :
    (tensorOneSlotAction H j T).domDomCongr σ = tensorOneSlotAction H (σ j) (T.domDomCongr σ) := by
  ext v
  simp only [ContinuousMultilinearMap.domDomCongr_apply, tensorOneSlotAction_apply]
  change T (Function.update (v ∘ σ) j (H *ᵥ v (σ j))) =
    T (Function.update v (σ j) (H *ᵥ v (σ j)) ∘ σ)
  rw [Function.update_comp_equiv, Equiv.symm_apply_apply]

theorem symmetricTensor_domDomCongr {r : ℕ} (T : TensorSpace r)
    (hT : T ∈ symmetricTensorSubmodule r) (σ : Equiv.Perm (Fin r)) : T.domDomCongr σ = T := by
  ext v
  exact hT v σ

theorem symmetricTensor_slot_pairing_eq_head {n : ℕ} (T : TensorSpace (n + 1))
    (hT : T ∈ symmetricTensorSubmodule (n + 1)) (H : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin (n + 1)) :
    tensorHSInner T (tensorOneSlotAction H j T) = tensorHSInner T (tensorOneSlotAction H 0 T) := by
  have h := tensorHSInner_permute T (tensorOneSlotAction H j T) (Equiv.swap j 0)
  rw [tensorOneSlotAction_permute, symmetricTensor_domDomCongr T hT, Equiv.swap_apply_left] at h
  exact h.symm

theorem tensorOneSlotAction_head_coordinates {n : ℕ} (T : TensorSpace (n + 1))
    (H : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) (a : Fin n → Fin 3) :
    tensorCoordinates (tensorOneSlotAction H 0 T) (Fin.cons i a) =
      ∑ j : Fin 3, H j i * tensorCoordinates T (Fin.cons j a) := by
  have he : tensorCoordinates (tensorOneSlotAction H 0 T) (Fin.cons i a) =
      tensorCoordinates (T.curryLeft (H *ᵥ Pi.single i (1 : ℝ))) a := by
    rw [tensorCoordinates_cons, tensorOneSlotAction_apply]
    simp only [tensorCoordinates, ContinuousMultilinearMap.curryLeft_apply, Fin.cons_zero]
    congr 1
    funext j
    refine Fin.cases ?_ (fun l => ?_) j <;> simp
  rw [he, tensor_curryLeft_coordinates]
  simp only [Matrix.mulVec_single_one, Matrix.transpose_apply]

theorem tensorHSInner_head_eq_trace_gram {n : ℕ} (T : TensorSpace (n + 1))
    (H : Matrix (Fin 3) (Fin 3) ℝ) :
    tensorHSInner T (tensorOneSlotAction H 0 T) = Matrix.trace (tensorContractionGram T * H) := by
  unfold tensorHSInner
  rw [← (tensorWordHeadTailEquiv n).symm.sum_comp
    (fun a => tensorCoordinates T a * tensorCoordinates (tensorOneSlotAction H 0 T) a)]
  change (∑ p : Fin 3 × (Fin n → Fin 3), tensorCoordinates T (Fin.cons p.1 p.2) *
    tensorCoordinates (tensorOneSlotAction H 0 T) (Fin.cons p.1 p.2)) = _
  rw [Fintype.sum_prod_type]
  simp only [tensorOneSlotAction_head_coordinates, Finset.mul_sum, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, tensorContractionGram_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem symmetricTensor_slot_pairing_eq_order_trace {n : ℕ} (T : TensorSpace (n + 1))
    (hT : T ∈ symmetricTensorSubmodule (n + 1)) (H : Matrix (Fin 3) (Fin 3) ℝ) :
    tensorHSInner T (tensorSlotAction H T) = (n + 1 : ℝ) * Matrix.trace (tensorContractionGram T * H) := by
  rw [tensorSlotAction, tensorHSInner_sum_right]
  simp only [symmetricTensor_slot_pairing_eq_head T hT H, tensorHSInner_head_eq_trace_gram,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

theorem hasDerivAt_symmetricTensor_energyCurve_zero {n : ℕ} (T : TensorSpace (n + 1))
    (hT : T ∈ symmetricTensorSubmodule (n + 1)) (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    HasDerivAt (tensorFrameEnergyCurve T H)
      (2 * (n + 1 : ℝ) * Matrix.trace (tensorContractionGram T * H)) 0 := by
  simpa only [symmetricTensor_slot_pairing_eq_order_trace T hT H, mul_assoc] using
    hasDerivAt_tensorFrameEnergyCurve_zero T H hH

theorem hasDerivAt_affineJet_energyCurve_gram_zero {k n : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    HasDerivAt (fun t : ℝ => (jetTensorHSNorm F c (B * NormedSpace.exp ℝ (t • H)) (n + 1)) ^ 2)
      (2 * (n + 1 : ℝ) * Matrix.trace (tensorContractionGram (affineJetTensor F c B (n + 1)) * H)) 0 := by
  rw [affineJet_energyCurve_eq]
  exact hasDerivAt_symmetricTensor_energyCurve_zero _ (affineJetTensor_mem_symmetricTensor F c B _) H hH

end PaperI
