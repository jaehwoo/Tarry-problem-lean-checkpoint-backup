import Revision.CapInterval
open Set MeasureTheory MvPolynomial
noncomputable section
namespace PaperI.CollarRevision
open BoundedCharacteristic CorridorBands ShortProjectionCaps ParabolicCollar CommonNullAssignment

/-- Lemma 3.16 before the preparation of any original-parent scalar roster. -/
theorem exact_geometric_cap (hQQE : PublishedQuantitativeRealQE) (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality) (hQE : PublishedRealSemialgebraicity) (s D K : ℕ) :
    ∃ fs fd n : ℕ, ∀ {ι : Type} [DecidableEq ι] {P m τ M δ Λ : ℝ} {C Cf k H so do' no : ℕ}
      {E A Ω : Set Plane} {d v : Plane → ℝ} {keep : Plane → Prop} {F : Plane → ℝ → ℝ}
      {labels : Finset ι} {rep : ι → Plane} {frame : Plane → Fin 6 → ℝ},
    PhaseCap P m τ Λ K k Cf H so do' no E Ω d v keep F labels rep →
    2≤P → 1≤m → 0<τ → τ≤m → τ+6*m+1<M → 0≤δ →
    P^C*δ*(2*m)≤Real.log 2 → P^C*δ*m^3≤1/16 →
    (∀ u∈E,ContDiffAt ℝ 1 d u) → (∀ u∈E,keep u) →
    (∀ q∈A,CertifiedBox P δ M C Cf E d v frame q) →
    Ω⊆A → IsConnected Ω → (∃ R,∀ q∈E,|q.1|≤R ∧ |q.2|≤R) →
    ∀ field : Finset (MvPolynomial (Fin 4) ℝ), field.card≤s → (∀ p∈field,p.totalDegree≤D) →
    PolynomialSignDetermined field (ShortProjectionCaps.fieldGraph E d v) →
    let I := project Ω F '' Ω
    let a := capLeft I m
    let b := capRight I m
    let z := midheight Ω
    let L := capLength I m
    let W := capWidth m
    I ⊆ Icc a b ∧ b-a=max m (horizontalSpan I) ∧ W≤L ∧ b-a≤L ∧ L≤4*(b-a) ∧
      (labels.card : ℝ)≤P^(4+(1+H+Cf+H)*k)*Λ*L*W ∧
      Nonempty (CollarCertificate (P:=P) (m:=m) (c:=(P^K)⁻¹) (a:=a) (b:=b) (z:=z) fs fd n K E d v keep) ∧
      (P^(3+(4+K+n)))⁻¹*(L*W)≤volume.real (capPatch a b z ((P^K)⁻¹*m) d v) := by
  obtain ⟨fs,fd,n,h⟩ := horizontal_algebraic_collar hQQE hCell hHardt hQE s D K
  refine ⟨fs,fd,n,?_⟩
  intro ι _ P m τ M δ Λ C Cf k H so do' no E A Ω d v keep F labels rep frame cap
    hP hm hτ hτm hM hδ hFlow hCubic hd hkeep box hΩ hConn hBound field hs hDeg hFmt I a b z L W
  obtain ⟨hLo,hHi⟩ := projection_bounded cap hτ hBound
  obtain ⟨hIn,hIncl,_⟩ := cap_geometry (hConn.nonempty.image (project Ω F)) hLo hHi (by linarith : 0≤m)
  have hEq : b-a=max m (horizontalSpan I) := cap_length I m
  have ha : a≤b := by linarith [le_max_left m (horizontalSpan I)]
  have hPos : 0<P := by linarith
  have hBoxes (t : ℝ) (ht : t∈Ioo a b) : CertifiedBox P δ (M-τ-m) C Cf E d v frame (horizontalSeed z t) :=
    Classical.choice (cap_horizontal_seed_boxes hP hm hτ hτm hM hδ hFlow hd hΩ hConn hBound box cap t
      (hIncl (Ioo_subset_Icc_self ht)))
  obtain ⟨cert⟩ := h hP hm hδ (inv_pos.mpr (pow_pos hPos K))
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))) le_rfl (by linarith : 4*m<M-τ-m)
    C Cf hCubic E d v frame keep hkeep ha hBoxes field hs hDeg hFmt
  have hL : L≤4*(b-a) := hEq.symm ▸ cap.scales.2.2.2.1
  have hW : W≤2*m := cap.scales.2.2.2.2.2
  refine ⟨hIn,hEq,cap.scales.2.1,hEq.symm ▸ cap.scales.2.2.1,hL,cap.count,⟨cert⟩,?_⟩
  have h8 : (8:ℝ)≤P^3 := (by norm_num : (8:ℝ)≤2^3).trans (pow_le_pow_left₀ (by norm_num) hP 3)
  have hS : L*W≤P^3*(m*(b-a)) := calc
    _ ≤ (4*(b-a))*(2*m) := mul_le_mul hL hW (roundedDyadicScale_pos _).le (mul_nonneg (by norm_num) (sub_nonneg.mpr ha))
    _ = 8*(m*(b-a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h8 (mul_nonneg (by linarith) (sub_nonneg.mpr ha))
  apply le_trans _ cert.area_lower
  rw [pow_add,mul_inv]
  calc
    _ ≤ ((P^3)⁻¹*(P^(4+K+n))⁻¹)*(P^3*(m*(b-a))) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by field_simp; ring

end PaperI.CollarRevision
