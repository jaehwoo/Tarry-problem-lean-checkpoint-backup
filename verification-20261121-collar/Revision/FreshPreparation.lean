import Revision.CapInterval

open Set MeasureTheory
open scoped ENNReal
noncomputable section

namespace PaperI.CollarRevision

open BoundedCharacteristic Preparation ParabolicCollar ShortProjectionCaps
open CommonNullAssignment PaperII.EndpointRangesWhole

/-- Only paths, counts and pointwise frame bounds descend from the larger cap.
The measure and all jet bounds come from the independently prepared smaller cap. -/
theorem assemble_inner_cap {ι κ₀ κ : Type} [DecidableEq ι] [Fintype κ₀] [Fintype κ]
    (C : ℝ) (n e₀ scalePow : ℕ) :
    ∃ e : ℕ, ∀ {d v c : Plane → ℝ} {F₀ : κ₀ → Plane → ℝ} {B₀ : κ₀ → ℝ}
      {F : κ → Plane → ℝ} {B : κ → ℝ} {BJ : ParabolicFieldIndex κ → ℝ}
      {a b z w P Λ ref y₀ z₀ U : ℝ} {parent : κ} {N : ℕ} {det : Coordinates → ℝ}
      {E : Set Plane} {keep : Plane → Prop} {X Y : NullScale}
      {labels : Finset ι} {rep : ι → Plane} {fixed : ι → Fin 6 → ℝ},
      2 ≤ P → 0 ≤ Λ → a < b → 0 < w → (∀ i, 0 ≤ B i) → (∀ i, BJ (Sum.inl i) = B i) →
      volume E ≠ ⊤ → X.S ≤ P^scalePow * ((b-a)*w) →
      Y.L ≤ 4*X.L → Y.S ≤ 4*X.S →
      (V : RelativeJointGerm N (horizontalSeed z) d v a b w C n det F BJ ref y₀ z₀ parent U) →
      (old : IndexedPreparedPatch d v c N P Λ e₀ E keep Y F₀ B₀ labels rep fixed) →
      (NullPatch.cap a b z w : NullPatch d v).region ⊆ old.prepared.patch.region →
      (∀ i ∈ labels, ∀ q ∈ old.prepared.patch.region,
        let g := fixedEndpointFrame (fixed i) c d q
        |g 5| ≤ P^e₀*Y.L ∧ |g 3| ≤ P^e₀*Y.L ∧ |g 4|+|g 4-g 3*g 5| ≤ P^e₀*Y.L^2) →
      Nonempty (ActualPreparedParabolic N e n (horizontalSeed z) d v c a b w C P Λ E keep X
        (.cap a b z w) F B BJ det ref y₀ z₀ parent U labels rep fixed) := by
  obtain ⟨q,hq⟩ := uniform_constant_le_power (max C (2*n))
  let e := q + scalePow + e₀ + 4
  refine ⟨e,?_⟩
  intro d v c F₀ B₀ F B BJ a b z w P Λ ref y₀ z₀ U parent N det E keep X Y labels rep fixed
    hP hΛ hab hw hB hBJ hE hScale hL hS V old hSub hRanges
  let patch : NullPatch d v := .cap a b z w
  let image := patch.evalAt '' V.base.good
  have hIn : image ⊆ patch.region := by
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨![u.1,u.2],V.base.contained hu,rfl⟩
  have hPatch : patch.region ⊆ E := hSub.trans old.prepared.inside
  have hFin : volume image ≠ ⊤ := ne_top_of_le_ne_top hE (measure_mono (hIn.trans hPatch))
  have hP₁ : 1 ≤ P := by linarith
  have hPos (j : ℕ) : 0 < P^j := pow_pos (by linarith) _
  have hx : 0 ≤ X.L := zero_le_one.trans X.L_one
  have hy : 0 ≤ Y.L := zero_le_one.trans Y.L_one
  have hxs : 0 ≤ X.S := zero_le_one.trans X.S_one
  have h4 : (2:ℝ)^4 ≤ P^4 := pow_le_pow_left₀ (by norm_num) hP 4
  have h16 : 16*P^e₀ ≤ P^e := by
    calc
      _ ≤ P^4*P^e₀ := mul_le_mul_of_nonneg_right (by norm_num at h4; exact h4) (hPos _).le
      _ = P^(4+e₀) := (pow_add ..).symm
      _ ≤ _ := pow_le_pow_right₀ hP₁ (by dsimp [e]; omega)
  have h4e : 4*P^e₀ ≤ P^e := (by nlinarith only [(hPos e₀).le] : 4*P^e₀ ≤ 16*P^e₀).trans h16
  have hLin : P^e₀*Y.L ≤ P^e*X.L := calc
    _ ≤ P^e₀*(4*X.L) := mul_le_mul_of_nonneg_left hL (hPos _).le
    _ = 4*P^e₀*X.L := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h4e hx
  have hQuad : P^e₀*Y.L^2 ≤ P^e*X.L^2 := calc
    _ ≤ P^e₀*(4*X.L)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hL 2) (hPos _).le
    _ = 16*P^e₀*X.L^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h16 (sq_nonneg _)
  have hCount : (labels.card : ℝ) ≤ P^e*Λ*X.S := calc
    _ ≤ P^e₀*Λ*Y.S := old.count
    _ ≤ P^e₀*Λ*(4*X.S) := mul_le_mul_of_nonneg_left hS (mul_nonneg (hPos _).le hΛ)
    _ = (4*P^e₀)*Λ*X.S := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4e hΛ) hxs
  have hG := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top n)) hFin)
    V.base.physical_area
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofNat] at hG
  rw [ENNReal.toReal_ofReal (mul_nonneg (sub_nonneg.mpr hab.le) hw.le)] at hG
  have hArea : (P^e)⁻¹*X.S ≤ volume.real image := by
    apply (inv_mul_le_iff₀ (hPos _)).mpr
    calc
      _ ≤ P^scalePow*((b-a)*w) := hScale
      _ ≤ P^scalePow*((2*(n:ℝ))*volume.real image) := mul_le_mul_of_nonneg_left hG (hPos _).le
      _ ≤ P^scalePow*(P^q*volume.real image) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (hq P hP)) ENNReal.toReal_nonneg) (hPos _).le
      _ = P^(scalePow+q)*volume.real image := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP₁ (by dsimp [e]; omega)) ENNReal.toReal_nonneg
  have hC : C ≤ P^e := ((le_max_left ..).trans (hq P hP)).trans
    (pow_le_pow_right₀ hP₁ (by dsimp [e]; omega))
  let prep : PreparedPhysicalPatch d v N P e E keep X F B :=
    ⟨patch,hPatch,fun u hu => old.prepared.admissible u (hSub hu),V.base.good,V.base.borel,
      V.base.contained,image,rfl,V.base.physical_borel,hIn,hArea,b-a,2*w,
      sub_pos.mpr hab,by positivity,fun u hu i j k hj => by
        have h := (V.base.bounds u hu).1 i j k hj
        rw [hBJ] at h
        exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (hB i))
          (mul_nonneg (pow_nonneg (sub_nonneg.mpr hab.le) _) (pow_nonneg (by positivity) _)))⟩
  let cert : IndexedPreparedPatch d v c N P Λ e E keep X F B labels rep fixed :=
    ⟨prep,hCount,fun i hi y hy' => (old.path i hi y (hSub hy')).mono hLin,fun i _ => by
      obtain ⟨hMeas,hEq⟩ := ModerateCorridor.physical_fixed_area (fixed i) c d V.base.physical_borel
      exact ⟨hMeas,congrArg ENNReal.toReal hEq⟩⟩
  refine ⟨⟨V,cert,rfl,rfl,rfl,rfl,?_⟩⟩
  intro i hi y hy'
  obtain ⟨hf,hd,hη⟩ := hRanges i hi y (hSub hy')
  exact ⟨hf.trans hLin,hd.trans hLin,hη.trans hQuad⟩

end PaperI.CollarRevision
