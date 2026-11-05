import PaperILean.OrderedIntegralPerturbation
import PaperILean.TensorFrameBounds

/-! I1480[363,533): polynomial perturbation of the actual original
upper-affine flow. Time reflection retains both endpoint directions.
All matrix norms below include all sixteen homogeneous-matrix entries. -/

noncomputable section
namespace PaperI.OriginalUpperFlowPerturbation
open Set

theorem ordered_signature_error_component
    (b c : ℝ → Fin 6 → ℝ) (a z M eps : ℝ) (haz : a ≤ z)
    (hb : ContinuousOn b (Icc a z)) (hc : ContinuousOn c (Icc a z))
    (hbM : ∀ t ∈ Icc a z, ∀ i, |b t i| ≤ M)
    (hcM : ∀ t ∈ Icc a z, ∀ i, |c t i| ≤ M)
    (herr : ∀ t ∈ Icc a z, ∀ i, |b t i - c t i| ≤ eps) (i : Fin 6) :
    |(originalUpperOrderedSignature b a z - originalUpperOrderedSignature c a z) i| ≤
      eps * ((z-a) + 4*M*(z-a)^2 + 3*M^2*(z-a)^3) := by
  obtain ⟨h1,h2,h3⟩ := OrderedIntegralPerturbation.ordered_integral_error_bounds
    b c a z M eps haz hb hc hbM hcM herr
  have ha : a ∈ Icc a z := ⟨le_rfl,haz⟩
  have hz : z ∈ Icc a z := ⟨haz,le_rfl⟩
  have hM : 0 ≤ M := (abs_nonneg (b a 0)).trans (hbM a ha 0)
  have heps : 0 ≤ eps := (abs_nonneg (b a 0-c a 0)).trans (herr a ha 0)
  have hL : 0 ≤ z-a := sub_nonneg.mpr haz
  have htwo : 0 ≤ 2*M*eps*(z-a)^2 := by positivity
  have hthree : 0 ≤ 3*M^2*eps*(z-a)^3 := by positivity
  have h1' (j : Fin 6) := h1 z hz j
  have h2' (j l : Fin 6) := h2 z hz j l
  have h3' (j l r : Fin 6) := h3 z hz j l r
  have hsingle (j : Fin 6) :
      |originalUpperIntegralOne b a z j-originalUpperIntegralOne c a z j| ≤
        eps * ((z-a)+4*M*(z-a)^2+3*M^2*(z-a)^3) := by
    nlinarith [h1' j]
  have hdouble (j l r : Fin 6) :
      |(originalUpperIntegralOne b a z j+originalUpperIntegralTwo b a z l r)-
        (originalUpperIntegralOne c a z j+originalUpperIntegralTwo c a z l r)| ≤
        eps * ((z-a)+4*M*(z-a)^2+3*M^2*(z-a)^3) := by
    rw [show (originalUpperIntegralOne b a z j+originalUpperIntegralTwo b a z l r)-
        (originalUpperIntegralOne c a z j+originalUpperIntegralTwo c a z l r) =
        (originalUpperIntegralOne b a z j-originalUpperIntegralOne c a z j)+
        (originalUpperIntegralTwo b a z l r-originalUpperIntegralTwo c a z l r) by ring]
    have h := (abs_add _ _).trans (add_le_add (h1' j) (h2' l r))
    nlinarith
  fin_cases i
  · exact hsingle 0
  · exact hdouble 1 0 3
  · change |(originalUpperIntegralOne b a z 2+originalUpperIntegralTwo b a z 0 4+
        originalUpperIntegralTwo b a z 1 5+originalUpperIntegralThree b a z 0 3 5)-
        (originalUpperIntegralOne c a z 2+originalUpperIntegralTwo c a z 0 4+
        originalUpperIntegralTwo c a z 1 5+originalUpperIntegralThree c a z 0 3 5)| ≤ _
    rw [show (originalUpperIntegralOne b a z 2+originalUpperIntegralTwo b a z 0 4+
        originalUpperIntegralTwo b a z 1 5+originalUpperIntegralThree b a z 0 3 5)-
        (originalUpperIntegralOne c a z 2+originalUpperIntegralTwo c a z 0 4+
        originalUpperIntegralTwo c a z 1 5+originalUpperIntegralThree c a z 0 3 5) =
        ((originalUpperIntegralOne b a z 2-originalUpperIntegralOne c a z 2)+
        (originalUpperIntegralTwo b a z 0 4-originalUpperIntegralTwo c a z 0 4)+
        (originalUpperIntegralTwo b a z 1 5-originalUpperIntegralTwo c a z 1 5))+
        (originalUpperIntegralThree b a z 0 3 5-originalUpperIntegralThree c a z 0 3 5) by ring]
    calc
      _ ≤ |originalUpperIntegralOne b a z 2-originalUpperIntegralOne c a z 2|+
          |originalUpperIntegralTwo b a z 0 4-originalUpperIntegralTwo c a z 0 4|+
          |originalUpperIntegralTwo b a z 1 5-originalUpperIntegralTwo c a z 1 5|+
          |originalUpperIntegralThree b a z 0 3 5-originalUpperIntegralThree c a z 0 3 5| :=
        (abs_add _ _).trans (add_le_add_right
          ((abs_add _ _).trans (add_le_add_right (abs_add _ _) _)) _)
      _ ≤ _ := by nlinarith [h1' 2,h2' 0 4,h2' 1 5,h3' 0 3 5]
  · exact hsingle 3
  · exact hdouble 4 3 5
  · exact hsingle 5

theorem relative_frame_error_component_le_of_le
    (g h b c : ℝ → Fin 6 → ℝ) (a z M eps : ℝ) (haz : a ≤ z)
    (hb : ContinuousOn b (Icc a z)) (hc : ContinuousOn c (Icc a z))
    (hg : ∀ t ∈ Icc a z, HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t)
    (hh : ∀ t ∈ Icc a z, HasDerivAt h (originalUpperBodyVelocity (h t) (c t)) t)
    (hbM : ∀ t ∈ Icc a z, ∀ i, |b t i| ≤ M)
    (hcM : ∀ t ∈ Icc a z, ∀ i, |c t i| ≤ M)
    (herr : ∀ t ∈ Icc a z, ∀ i, |b t i-c t i| ≤ eps) (i : Fin 6) :
    |(originalUpperRelativeFrame (g a) (g z)-originalUpperRelativeFrame (h a) (h z)) i| ≤
      eps * ((z-a)+4*M*(z-a)^2+3*M^2*(z-a)^3) := by
  rw [originalUpperRelativeFrame_ordered_integrals g b a z haz hb hg,
    originalUpperRelativeFrame_ordered_integrals h c a z haz hc hh]
  exact ordered_signature_error_component b c a z M eps haz hb hc hbM hcM herr i

theorem originalUpperBodyVelocity_neg (g b : Fin 6 → ℝ) :
    originalUpperBodyVelocity g (-b) = -originalUpperBodyVelocity g b := by
  ext i
  fin_cases i <;> simp [originalUpperBodyVelocity] <;> ring

theorem reflected_hasDerivAt (g b : ℝ → Fin 6 → ℝ) (a z t : ℝ)
    (hg : HasDerivAt g
      (originalUpperBodyVelocity (g (a+z-t)) (b (a+z-t))) (a+z-t)) :
    HasDerivAt (fun s => g (a+z-s))
      (originalUpperBodyVelocity (g (a+z-t)) (-b (a+z-t))) t := by
  have hr : HasDerivAt (fun s : ℝ => a+z-s) (-1) t :=
    (hasDerivAt_id t).const_sub (a+z)
  simpa only [Function.comp_def, neg_one_smul, originalUpperBodyVelocity_neg] using
    hg.scomp t hr

theorem relative_frame_reverse_error_component_le_of_le
    (g h b c : ℝ → Fin 6 → ℝ) (a z M eps : ℝ) (haz : a ≤ z)
    (hb : ContinuousOn b (Icc a z)) (hc : ContinuousOn c (Icc a z))
    (hg : ∀ t ∈ Icc a z, HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t)
    (hh : ∀ t ∈ Icc a z, HasDerivAt h (originalUpperBodyVelocity (h t) (c t)) t)
    (hbM : ∀ t ∈ Icc a z, ∀ i, |b t i| ≤ M)
    (hcM : ∀ t ∈ Icc a z, ∀ i, |c t i| ≤ M)
    (herr : ∀ t ∈ Icc a z, ∀ i, |b t i-c t i| ≤ eps) (i : Fin 6) :
    |(originalUpperRelativeFrame (g z) (g a)-originalUpperRelativeFrame (h z) (h a)) i| ≤
      eps * ((z-a)+4*M*(z-a)^2+3*M^2*(z-a)^3) := by
  have hr : MapsTo (fun t : ℝ => a+z-t) (Icc a z) (Icc a z) := by
    intro t ht
    change a ≤ a+z-t ∧ a+z-t ≤ z
    constructor <;> linarith [ht.1,ht.2]
  have hrc : ContinuousOn (fun t : ℝ => a+z-t) (Icc a z) :=
    (continuous_const.sub continuous_id).continuousOn
  have hb' : ContinuousOn (fun t => -b (a+z-t)) (Icc a z) := (hb.comp hrc hr).neg
  have hc' : ContinuousOn (fun t => -c (a+z-t)) (Icc a z) := (hc.comp hrc hr).neg
  have h := relative_frame_error_component_le_of_le
    (fun t => g (a+z-t)) (fun t => h (a+z-t))
    (fun t => -b (a+z-t)) (fun t => -c (a+z-t)) a z M eps haz hb' hc'
    (fun t ht => reflected_hasDerivAt g b a z t (hg _ (hr ht)))
    (fun t ht => reflected_hasDerivAt h c a z t (hh _ (hr ht)))
    (fun t ht j => by simpa only [Pi.neg_apply, abs_neg] using hbM _ (hr ht) j)
    (fun t ht j => by simpa only [Pi.neg_apply, abs_neg] using hcM _ (hr ht) j)
    (fun t ht j => by simpa only [Pi.neg_apply, neg_sub_neg, abs_sub_comm] using (herr _ (hr ht) j)) i
  simpa only [add_sub_cancel_right, add_sub_cancel_left] using h

theorem relative_frame_error_component_le
    (g h b c : ℝ → Fin 6 → ℝ) (a z M eps : ℝ)
    (hb : ContinuousOn b (uIcc a z)) (hc : ContinuousOn c (uIcc a z))
    (hg : ∀ t ∈ uIcc a z, HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t)
    (hh : ∀ t ∈ uIcc a z, HasDerivAt h (originalUpperBodyVelocity (h t) (c t)) t)
    (hbM : ∀ t ∈ uIcc a z, ∀ i, |b t i| ≤ M)
    (hcM : ∀ t ∈ uIcc a z, ∀ i, |c t i| ≤ M)
    (herr : ∀ t ∈ uIcc a z, ∀ i, |b t i-c t i| ≤ eps) (i : Fin 6) :
    |(originalUpperRelativeFrame (g a) (g z)-originalUpperRelativeFrame (h a) (h z)) i| ≤
      eps * (|z-a|+4*M*|z-a|^2+3*M^2*|z-a|^3) := by
  rcases le_total a z with haz | hza
  · rw [uIcc_of_le haz] at hb hc hg hh hbM hcM herr
    simpa only [abs_of_nonneg (sub_nonneg.mpr haz)] using
      relative_frame_error_component_le_of_le g h b c a z M eps haz hb hc hg hh hbM hcM herr i
  · rw [uIcc_of_ge hza] at hb hc hg hh hbM hcM herr
    have habs : |z-a| = a-z := by rw [abs_of_nonpos (sub_nonpos.mpr hza)]; ring
    simpa only [habs] using
      relative_frame_reverse_error_component_le_of_le g h b c z a M eps hza hb hc hg hh hbM hcM herr i

/-- The six strict-upper entries are exactly the varying entries of the
literal homogeneous affine matrix. This is an equality of Euclidean norms. -/
theorem homogeneous_matrix_sub_norm (x y : Fin 6 → ℝ) :
    coordinateL2Norm (fun ij : Fin 4 × Fin 4 =>
      (originalAffineHomogeneousMatrix x-originalAffineHomogeneousMatrix y) ij.1 ij.2) =
      coordinateL2Norm (x-y) := by
  unfold coordinateL2Norm
  congr 1
  simp [Fintype.sum_prod_type, Fin.sum_univ_succ, originalAffineHomogeneousMatrix]
  ring

/-- The complete actual-flow perturbation stage, for arbitrary endpoints
and independent initial frames, in both six-coordinate and full matrix norms. -/
theorem original_upper_flow_perturbation_stage
    (g h b c : ℝ → Fin 6 → ℝ) (a z M eps : ℝ)
    (hb : ContinuousOn b (uIcc a z)) (hc : ContinuousOn c (uIcc a z))
    (hg : ∀ t ∈ uIcc a z, HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t)
    (hh : ∀ t ∈ uIcc a z, HasDerivAt h (originalUpperBodyVelocity (h t) (c t)) t)
    (hbM : ∀ t ∈ uIcc a z, ∀ i, |b t i| ≤ M)
    (hcM : ∀ t ∈ uIcc a z, ∀ i, |c t i| ≤ M)
    (herr : ∀ t ∈ uIcc a z, ∀ i, |b t i-c t i| ≤ eps) :
    coordinateL2Norm (originalUpperRelativeFrame (g a) (g z)-
      originalUpperRelativeFrame (h a) (h z)) ≤
      Real.sqrt 6 * (eps * (|z-a|+4*M*|z-a|^2+3*M^2*|z-a|^3)) ∧
    coordinateL2Norm (fun ij : Fin 4 × Fin 4 =>
      (originalAffineHomogeneousMatrix (originalUpperRelativeFrame (g a) (g z))-
       originalAffineHomogeneousMatrix (originalUpperRelativeFrame (h a) (h z))) ij.1 ij.2) ≤
      Real.sqrt 6 * (eps * (|z-a|+4*M*|z-a|^2+3*M^2*|z-a|^3)) := by
  have hM : 0 ≤ M := (abs_nonneg (b a 0)).trans (hbM a left_mem_uIcc 0)
  have heps : 0 ≤ eps := (abs_nonneg (b a 0-c a 0)).trans (herr a left_mem_uIcc 0)
  have hbound : 0 ≤ eps * (|z-a|+4*M*|z-a|^2+3*M^2*|z-a|^3) := by positivity
  have hn := coordinateL2Norm_le_of_component_bound _ _ hbound
    (relative_frame_error_component_le g h b c a z M eps hb hc hg hh hbM hcM herr)
  norm_num only [Fintype.card_fin] at hn
  exact ⟨hn, by rw [homogeneous_matrix_sub_norm]; exact hn⟩

end PaperI.OriginalUpperFlowPerturbation
