import PaperILean.OriginalQuadraticGaussBox
import PaperILean.OriginalUpperNormalPullback

/-! I702-I707/I848/I1305: every nonconstant coefficient of the original
quadratic reference phase is independent of its Gauss parameter. The profile
is not replaced by a normal derivative. A selected normal root and its exact
pivot propagate over the whole reference graph; no lower jets must vanish.
The quantitative perturbation and full-parent admissibility steps are open. -/
noncomputable section
namespace PaperI

theorem originalQuadraticGaussFrame_normalized_phase {k : ℕ}
    (F : CoefficientSpace k) (f : ℝ → ℝ) (r b v t w η lam mu K : ℝ) (hr : r ≠ 0)
    (hF : ∀ x : Fin 3 → ℝ,
      phase F x = f (originalQuadraticInvariant r b v t w x)+lam*x 1+mu*x 2+K)
    (a : Fin 2 → ℝ) (x : Fin 3 → ℝ) :
    phase (originalUpperCoefficientPullback F (originalQuadraticGaussFrame r b v t w η a)) x =
      f (η+x 0-r/2*(x 1)^2-originalQuadraticSchur r b v/2*(x 2)^2)-f η+
        lam*x 1+(mu-lam*b/r)*x 2 := by
  let g := originalQuadraticGaussFrame r b v t w η a
  have hz : (![g 2,g 4,g 5] : Fin 3 → ℝ) = originalUpperAffineEval g 0 := by
    simp [originalUpperAffineEval]
  rw [originalUpperCoefficientPullback_phase F g x,hz,hF,hF]
  dsimp only [g]
  rw [originalQuadraticInvariant_frame r b v t w η hr,
    originalQuadraticInvariant_frame r b v t w η hr]
  simp only [Pi.zero_apply,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,sub_zero]
  rw [originalQuadraticGaussFrame_formula,originalGaussNormalFrame_eval,
    originalGaussNormalFrame_eval]
  simp
  ring

theorem originalQuadraticGaussFrame_coefficients_constant {k : ℕ}
    (F : CoefficientSpace k) (f : ℝ → ℝ) (r b v t w η lam mu K : ℝ) (hr : r ≠ 0)
    (hF : ∀ x : Fin 3 → ℝ,
      phase F x = f (originalQuadraticInvariant r b v t w x)+lam*x 1+mu*x 2+K)
    (a q : Fin 2 → ℝ) :
    originalUpperCoefficientPullback F (originalQuadraticGaussFrame r b v t w η a) =
      originalUpperCoefficientPullback F (originalQuadraticGaussFrame r b v t w η q) := by
  apply coefficient_ext
  intro x
  rw [originalQuadraticGaussFrame_normalized_phase F f r b v t w η lam mu K hr hF,
    originalQuadraticGaussFrame_normalized_phase F f r b v t w η lam mu K hr hF]

theorem originalQuadraticGaussFrame_normal_restriction {k : ℕ}
    (F : CoefficientSpace k) (f : ℝ → ℝ) (r b v t w η lam mu K : ℝ) (hr : r ≠ 0)
    (hF : ∀ x : Fin 3 → ℝ,
      phase F x = f (originalQuadraticInvariant r b v t w x)+lam*x 1+mu*x 2+K)
    (n : ℕ) (hn : 1 ≤ n) (a : Fin 2 → ℝ) :
    originalNormalPhase F n
      ![originalQuadraticGraph r b v t w η ![originalQuadraticGaussInverse r b t a,a 1],
        originalQuadraticGaussInverse r b t a,a 1] = originalNormalPhase F n ![η,0,0] := by
  have h := congrArg (fun G : CoefficientSpace k => originalNormalPhase G n 0)
    (originalQuadraticGaussFrame_coefficients_constant F f r b v t w η lam mu K hr hF a ![t,0])
  dsimp only at h
  rw [originalUpperCoefficientPullback_normal F _ n hn,
    originalUpperCoefficientPullback_normal F _ n hn,
    originalQuadraticGaussFrame_origin,originalQuadraticGaussFrame_origin] at h
  simpa [originalQuadraticGaussInverse,originalQuadraticGraph] using h

theorem originalQuadraticGraph_normal_restriction {k : ℕ}
    (F : CoefficientSpace k) (f : ℝ → ℝ) (r b v t w η lam mu K : ℝ) (hr : r ≠ 0)
    (hF : ∀ x : Fin 3 → ℝ,
      phase F x = f (originalQuadraticInvariant r b v t w x)+lam*x 1+mu*x 2+K)
    (n : ℕ) (hn : 1 ≤ n) (a : Fin 2 → ℝ) :
    originalNormalPhase F n ![originalQuadraticGraph r b v t w η a,a 0,a 1] =
      originalNormalPhase F n ![η,0,0] := by
  have h := originalQuadraticGaussFrame_normal_restriction F f r b v t w η lam mu K hr hF n hn
    ![originalGaussCy (originalQuadraticGraph r b v t w η) a,a 1]
  rw [originalQuadraticGaussInverse_left r b v t w η hr] at h
  have he : (![a 0,a 1] : Fin 2 → ℝ) = a := by ext i; fin_cases i <;> rfl
  change originalNormalPhase F n
    ![originalQuadraticGraph r b v t w η ![a 0,a 1],a 0,a 1] = _ at h
  rw [he] at h
  simpa only [he] using h

theorem originalQuadraticGaussFrame_order_m_sheet {k : ℕ}
    (F : CoefficientSpace k) (f : ℝ → ℝ) (r b v t w η lam mu K : ℝ) (hr : r ≠ 0)
    (hF : ∀ x : Fin 3 → ℝ,
      phase F x = f (originalQuadraticInvariant r b v t w x)+lam*x 1+mu*x 2+K)
    (m : ℕ) (horder : 2 ≤ m ∧ m ≤ k/2)
    (hroot : originalNormalPhase F (m-1) ![η,0,0] = 0)
    (hpivot : originalNormalPhase F m ![η,0,0] ≠ 0) (a : Fin 2 → ℝ) :
    originalNormalPhase F (m-1)
      ![originalQuadraticGraph r b v t w η ![originalQuadraticGaussInverse r b t a,a 1],
        originalQuadraticGaussInverse r b t a,a 1] = 0 ∧
    originalNormalPhase F m
      ![originalQuadraticGraph r b v t w η ![originalQuadraticGaussInverse r b t a,a 1],
        originalQuadraticGaussInverse r b t a,a 1] = originalNormalPhase F m ![η,0,0] ∧
    originalNormalPhase F m
      ![originalQuadraticGraph r b v t w η ![originalQuadraticGaussInverse r b t a,a 1],
        originalQuadraticGaussInverse r b t a,a 1] ≠ 0 ∧
    originalGaussR (originalQuadraticGraph r b v t w η)
      ![originalQuadraticGaussInverse r b t a,a 1] = r ∧
    originalGaussCy (originalQuadraticGraph r b v t w η)
      ![originalQuadraticGaussInverse r b t a,a 1] = a 0 := by
  have hn : 1 ≤ m-1 := by omega
  have hm : 1 ≤ m := by omega
  rw [originalQuadraticGaussFrame_normal_restriction F f r b v t w η lam mu K hr hF (m-1) hn,
    originalQuadraticGaussFrame_normal_restriction F f r b v t w η lam mu K hr hF m hm]
  exact ⟨hroot,rfl,hpivot,originalQuadraticGraph_R r b v t w η _,
    originalQuadraticGaussInverse_right r b v t w η hr a⟩

end PaperI
