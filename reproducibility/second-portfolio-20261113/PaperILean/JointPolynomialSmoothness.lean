import PaperILean.FrameEnergySmoothness

/-! Joint analytic dependence on the entire coefficient vector, center and frame.
The tensors remain the actual iterated Frechet derivatives, not replacements.
All natural degrees and derivative orders, including empty sums, are allowed. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem contDiff_phase_joint {k : ℕ} :
    ContDiff ℝ ⊤ (fun p : CoefficientSpace k × PhysicalSpace => phase p.1 p.2) := by
  classical
  unfold phase
  apply ContDiff.sum
  intro a _
  exact ((contDiff_apply ℝ ℝ a).comp contDiff_fst).mul
    (contDiff_prod (fun i _ => ((contDiff_apply ℝ ℝ i).comp contDiff_snd).pow _))

theorem contDiff_iteratedFDeriv_phase_joint {k : ℕ} (r : ℕ) :
    ContDiff ℝ ⊤ (fun p : CoefficientSpace k × PhysicalSpace =>
      iteratedFDeriv ℝ r (phase p.1) p.2) := by
  induction r with
  | zero =>
      exact (continuousMultilinearCurryFin0 ℝ PhysicalSpace ℝ).symm.toContinuousLinearEquiv.contDiff.comp
        contDiff_phase_joint
  | succ r ih =>
      have hp : ContDiff ℝ ⊤ (fun p : (CoefficientSpace k × PhysicalSpace) × PhysicalSpace =>
          iteratedFDeriv ℝ r (phase p.1.1) p.2) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ⊤ (fun p : CoefficientSpace k × PhysicalSpace =>
          fderiv ℝ (iteratedFDeriv ℝ r (phase p.1)) p.2) :=
        hp.fderiv (f := fun p x => iteratedFDeriv ℝ r (phase p.1) x)
          contDiff_snd (by simp : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (r + 1) => PhysicalSpace) ℝ).symm.toContinuousLinearEquiv.contDiff.comp hd

theorem contDiff_tensor_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℕ} {T : E → TensorSpace r} {v : E → Fin r → PhysicalSpace}
    (hT : ContDiff ℝ ⊤ T) (hv : ContDiff ℝ ⊤ v) :
    ContDiff ℝ ⊤ (fun x => T x (v x)) := by
  induction r with
  | zero =>
      have he : (fun x => T x (v x)) = (fun x => T x 0) := by
        funext x
        rw [Subsingleton.elim (v x) 0]
      rw [he]
      exact (continuousMultilinearCurryFin0 ℝ PhysicalSpace ℝ).toContinuousLinearEquiv.contDiff.comp hT
  | succ r ih =>
      have hc : ContDiff ℝ ⊤ (fun x => ((T x).curryLeft : PhysicalSpace →L[ℝ] TensorSpace r)) := by
        have hL : ContDiff ℝ ⊤ (continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (r + 1) => PhysicalSpace) ℝ) :=
          LinearIsometryEquiv.contDiff (𝕜 := ℝ) (E := TensorSpace (r + 1))
            (F := PhysicalSpace →L[ℝ] TensorSpace r) (n := ⊤)
            (continuousMultilinearCurryLeftEquiv ℝ
              (fun _ : Fin (r + 1) => PhysicalSpace) ℝ)
        convert hL.comp hT using 1
      have ht : ContDiff ℝ ⊤ (fun x => Fin.tail (v x)) :=
        contDiff_pi.mpr (fun j => (contDiff_apply ℝ PhysicalSpace j.succ).comp hv)
      have hh := ih (hc.clm_apply ((contDiff_apply ℝ PhysicalSpace 0).comp hv)) ht
      simpa only [Function.comp_def, ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail] using hh

theorem contDiff_jetTensorComponent_joint {k : ℕ} (r : ℕ) (a : Fin r → Fin 3) :
    ContDiff ℝ ⊤ (fun p : (CoefficientSpace k × PhysicalSpace) × Matrix (Fin 3) (Fin 3) ℝ =>
      jetTensorComponent p.1.1 p.1.2 p.2 r a) := by
  unfold jetTensorComponent
  apply contDiff_tensor_apply ((contDiff_iteratedFDeriv_phase_joint r).comp contDiff_fst)
  simp only [Matrix.mulVec_single_one]
  exact contDiff_pi.mpr (fun j => contDiff_pi.mpr
    (fun i => (contDiff_matrix_entry i (a j)).comp contDiff_snd))

theorem contDiff_jetTensorHSNorm_sq_joint {k : ℕ} (r : ℕ) :
    ContDiff ℝ ⊤ (fun p : (CoefficientSpace k × PhysicalSpace) × Matrix (Fin 3) (Fin 3) ℝ =>
      (jetTensorHSNorm p.1.1 p.1.2 p.2 r) ^ 2) := by
  simp only [jetTensorHSNorm_sq]
  exact ContDiff.sum (fun a _ => (contDiff_jetTensorComponent_joint r a).pow 2)

end PaperI
