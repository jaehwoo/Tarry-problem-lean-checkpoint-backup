import PaperILean.OriginalAssignedComponentPacking

/-! I1265 algebraic transfers to reported rounded scales. The physical strip
and centerline are not enlarged or moved. Losses are displayed explicitly. -/
noncomputable section
namespace PaperI
open Set

theorem OriginalBorelStripFamily.PhysicalPreparedAt.mono_constant
    {Ω : Type*} [MeasurableSpace Ω] {B : OriginalBorelStripFamily Ω}
    {N : ℕ} {C C' L : ℝ} {ω : Ω}
    (h : B.PhysicalPreparedAt N C L ω) (hL : 0<L) (hC : C≤C') :
    B.PhysicalPreparedAt N C' L ω := by
  have hbound (j : ℕ) : C*L/L^j≤C'*L/L^j :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hL.le) (pow_nonneg hL.le j)
  exact ⟨h.1,h.2.1,fun x hx j hj => (h.2.2.1 x hx j hj).trans (hbound j),
    fun x hx j hj hjN => (h.2.2.2 x hx j hj hjN).trans (hbound j)⟩

theorem OriginalBorelStripFamily.PhysicalPreparedAt.rescale
    {Ω : Type*} [MeasurableSpace Ω] {B : OriginalBorelStripFamily Ω}
    {N : ℕ} {C A L0 L : ℝ} {ω : Ω}
    (h : B.PhysicalPreparedAt N C L0 ω) (hC : 0≤C) (hA : 1≤A)
    (hL0 : 0<L0) (hL : L0≤L) (hcomp : L≤A*L0) :
    B.PhysicalPreparedAt N (C*A^N) L ω := by
  have hb (j : ℕ) (hj : j≤N) :=
    prepared_arc_derivative_scale_comparison hC hA hL0 hL hcomp hj
  exact ⟨h.1,h.2.1,fun x hx j hj => (h.2.2.1 x hx j hj).trans (hb j hj),
    fun x hx j hj hjN => (h.2.2.2 x hx j hj hjN).trans (hb j hjN)⟩

theorem original_scaled_length_lower {D A L0 L Q len : ℝ}
    (hD : 0<D) (hA : 0<A) (hL0 : 0≤L0) (hL : 0≤L)
    (hcomp : L≤A*L0) (hQ : D*A≤Q) (hlen : L0/D≤len) : L/Q≤len := by
  have hQ0 : 0<Q := (mul_pos hD hA).trans_le hQ
  apply le_trans (div_le_div_of_nonneg_right hcomp hQ0.le)
  apply le_trans _ hlen
  apply (div_le_div_iff₀ hQ0 hD).mpr
  convert mul_le_mul_of_nonneg_right hQ hL0 using 1 <;> ring

theorem original_scaled_area_lower {D A L0 W0 L W Q area : ℝ}
    (hD : 0<D) (hA : 0<A) (hL0 : 0≤L0) (hW0 : 0≤W0)
    (hL : 0≤L) (hW : 0≤W) (hcompL : L≤A*L0) (hcompW : W≤A*W0)
    (hQ : D*A^2≤Q) (harea : L0*W0/D≤area) : L*W/Q≤area := by
  have hQ0 : 0<Q := (mul_pos hD (pow_pos hA 2)).trans_le hQ
  have hprod : L*W≤(A*L0)*(A*W0) :=
    mul_le_mul hcompL hcompW hW (mul_nonneg hA.le hL0)
  apply le_trans (div_le_div_of_nonneg_right hprod hQ0.le)
  apply le_trans _ harea
  apply (div_le_div_iff₀ hQ0 hD).mpr
  convert mul_le_mul_of_nonneg_right hQ (mul_nonneg hL0 hW0) using 1 <;> ring

theorem original_uniform_real_rounded_scales (c : ℝ) :
    ∃ a : ℕ, ∀ P : ℝ, 2≤P → ∀ W0 L0 : ℝ, P^(-c)/2≤W0 → W0≤L0 →
      roundedDyadicScale W0≤P^a*W0 ∧ roundedDyadicScale L0≤P^a*L0 := by
  obtain ⟨q,hq⟩ := original_inverse_real_power_minorant c
  obtain ⟨m,hm⟩ := uniform_roundedDyadicScale_power_comparison (1/2) (by norm_num)
  refine ⟨m+q+1,?_⟩
  intro P hP W0 L0 hW hL
  have hw : (1/2 : ℝ)*(P^q)⁻¹≤W0 := by linarith [hq P hP]
  exact ⟨(hm P q hP W0 hw).2.2,(hm P q hP L0 (hw.trans hL)).2.2⟩

end PaperI
