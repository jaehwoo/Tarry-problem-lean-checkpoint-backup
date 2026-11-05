import PaperILean.OriginalUpperIntegralBounds

/-! Endpoint extension of the original closed-C1 relative-frame estimate.
The path need only be continuous at the analytic-piece endpoints. -/
noncomputable section
namespace PaperI
open Set MeasureTheory

private theorem upperComp_continuous :
    Continuous (fun p : (Fin 6 → ℝ) × (Fin 6 → ℝ) =>
      originalUpperAffineComp p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [originalUpperAffineComp] <;> fun_prop

private theorem upperInv_continuous :
    Continuous (originalUpperAffineInv : (Fin 6 → ℝ) → (Fin 6 → ℝ)) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [originalUpperAffineInv] <;> fun_prop

private theorem upperRelative_continuous :
    Continuous (fun p : (Fin 6 → ℝ) × (Fin 6 → ℝ) =>
      originalUpperRelativeFrame p.1 p.2) := by
  exact upperComp_continuous.comp
    ((upperInv_continuous.comp continuous_fst).prodMk continuous_snd)

/-- A uniform bound on all compact interior increments passes to both
endpoints. In particular no endpoint derivative or endpoint body continuity
is silently required by this bridge. -/
theorem originalUpperRelativeFrame_endpoint_bound
    (g : ℝ → Fin 6 → ℝ) (a z C : ℝ) (haz : a < z)
    (hg : ContinuousOn g (Icc a z))
    (hcompact : ∀ u ∈ Ioo a z, ∀ v ∈ Ioo a z, u ≤ v →
      ‖originalUpperRelativeFrame (g u) (g v)‖ ≤ C) :
    ‖originalUpperRelativeFrame (g a) (g z)‖ ≤ C := by
  let m : ℝ := (a+z)/2
  have ham : a < m := by dsimp [m]; linarith
  have hmz : m < z := by dsimp [m]; linarith
  let D : Set (ℝ × ℝ) := Icc a z ×ˢ Icc a z
  let f : ℝ × ℝ → ℝ := fun p => ‖originalUpperRelativeFrame (g p.1) (g p.2)‖
  have hfst : ContinuousOn (fun p : ℝ × ℝ => g p.1) D :=
    hg.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hsnd : ContinuousOn (fun p : ℝ × ℝ => g p.2) D :=
    hg.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hf : ContinuousOn f D :=
    (upperRelative_continuous.comp_continuousOn (hfst.prodMk hsnd)).norm
  have hclosed : IsClosed (D ∩ f ⁻¹' Iic C) :=
    hf.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_Icc) isClosed_Iic
  have hsub : Ioo a m ×ˢ Ioo m z ⊆ D ∩ f ⁻¹' Iic C := by
    intro p hp
    have hu : p.1 ∈ Ioo a z := ⟨hp.1.1, hp.1.2.trans hmz⟩
    have hv : p.2 ∈ Ioo a z := ⟨ham.trans hp.2.1, hp.2.2⟩
    exact ⟨⟨⟨hu.1.le,hu.2.le⟩,⟨hv.1.le,hv.2.le⟩⟩,
      hcompact p.1 hu p.2 hv (hp.1.2.trans hp.2.1).le⟩
  have hp : (a,z) ∈ closure (Ioo a m ×ˢ Ioo m z) := by
    rw [closure_prod_eq, closure_Ioo ham.ne, closure_Ioo hmz.ne]
    exact ⟨⟨le_rfl,ham.le⟩,⟨hmz.le,le_rfl⟩⟩
  exact ((closure_minimal hsub hclosed) hp).2

/-- The saved ordered-integral bound applies on compact subintervals of an
open analytic piece, and its polynomial bound then extends to the endpoints.
The single body field is continuous only inside the piece. -/
theorem originalUpperRelativeFrame_open_piece_bound
    (g b : ℝ → Fin 6 → ℝ) (w : ℝ → ℝ) (a z L : ℝ)
    (haz : a < z) (hL : 0 ≤ L)
    (hg : ContinuousOn g (Icc a z))
    (hb : ContinuousOn b (Ioo a z))
    (hderiv : ∀ t ∈ Ioo a z,
      HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t)
    (hw : ∀ u ∈ Ioo a z, ∀ v ∈ Ioo a z, u ≤ v →
      IntervalIntegrable w volume u v)
    (hw0 : ∀ s ∈ Ioo a z, 0 ≤ w s)
    (hbw : ∀ s ∈ Ioo a z, ∀ i : Fin 6, |b s i| ≤ w s)
    (hint : ∀ u ∈ Ioo a z, ∀ v ∈ Ioo a z, u ≤ v →
      (∫ s in u..v, w s) ≤ L) :
    ‖originalUpperRelativeFrame (g a) (g z)‖ ≤ L*(1+L)^2 := by
  apply originalUpperRelativeFrame_endpoint_bound g a z _ haz hg
  intro u hu v hv huv
  have hsub : Icc u v ⊆ Ioo a z := fun s hs =>
    ⟨hu.1.trans_le hs.1, hs.2.trans_lt hv.2⟩
  have hlocal := (originalUpperRelativeFrame_norm_bounds g b w u v huv
    (hb.mono hsub) (fun t ht => hderiv t (hsub ht)) (hw u hu v hv huv)
    (fun s hs => hw0 s (hsub hs)) (fun s hs => hbw s (hsub hs))).1
  have h0 : 0 ≤ ∫ s in u..v, w s :=
    intervalIntegral.integral_nonneg huv (fun s hs => hw0 s (hsub hs))
  have hi := hint u hu v hv huv
  have hs : (1 + ∫ s in u..v, w s)^2 ≤ (1+L)^2 := by nlinarith
  exact hlocal.trans (mul_le_mul hi hs (sq_nonneg _) hL)

end PaperI
