import PaperILean.BufferedComponentTubeArea
import PaperILean.PlanarGridAreaCount

/-! I1261: the actual local-width enlargement has a finite delta-grid cover;
apply precisely the assumed square-local label count. The lower-width
constant c is retained: c*delta<=W does not mean delta<=W. -/

noncomputable section
namespace PaperI
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

theorem local_width_grid_enlargement_subset
    (C : Set (EuclideanSpace ℝ (Fin 2))) {b c δ W : ℝ}
    (hb : 0 ≤ b) (hc : 0 < c) (hδ : 0 < δ) (hW : 0 < W) (hwidth : c*δ ≤ W) :
    cthickening (2*δ) (cthickening (b*W) C) ⊆ cthickening ((b+2/c)*W) C := by
  have hd : δ ≤ W/c := (le_div_iff₀ hc).mpr (by nlinarith [hwidth])
  refine (cthickening_cthickening_subset (by positivity) (mul_nonneg hb hW.le) C).trans
    (cthickening_mono ?_ C)
  calc
    2*δ+b*W ≤ 2*(W/c)+b*W := by linarith
    _ = (b+2/c)*W := by ring

theorem published_uniform_bufferedComponent_grid_cover
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hMono : PublishedOneVariableMonotonicity)
    (s D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Set (EuclideanSpace ℝ (Fin 2)))
      (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) →
      IsOpen E → Bornology.IsBounded E → ∀ b c δ W : ℝ,
      0 ≤ b → 0 < c → 0 < δ → 0 < W → c*δ ≤ W →
      ∀ (z : EuclideanSpace ℝ (Fin 2)) (o : Fin 2 → ℝ),
      ∃ S : Finset (Fin 2 → ℤ),
        (∀ k, k ∈ S ↔ k ∈ planarGridTouched o δ (cthickening (b*W) (bufferedBandComponent E W z))) ∧
        cthickening (b*W) (bufferedBandComponent E W z) ⊆ ⋃ k ∈ S, planarGridCell o δ k ∧
        (⋃ k ∈ S, planarGridCell o δ k) ⊆ cthickening ((b+2/c)*W) (bufferedBandComponent E W z) ∧
        (S.card : ℝ) ≤ K*(b+2/c+5)*(b+2/c+4)*bufferedComponentScale E W z*W/δ^2 := by
  obtain ⟨K,hK,harea⟩ := published_uniform_bufferedComponent_enlargement_area
    hCAD hCell hHardt hQE hMono s D
  refine ⟨K,hK,?_⟩
  intro E A hAc hAd hA ho hb b c δ W hb0 hc hδ hW hwidth z o
  have hsub := local_width_grid_enlargement_subset (bufferedBandComponent E W z)
    hb0 hc hδ hW hwidth
  have hbig := harea E A hAc hAd hA ho hb (b+2/c) W (by positivity) hW z
  have hB : 0 ≤ K*(b+2/c+5)*(b+2/c+4)*bufferedComponentScale E W z*W := by
    have := bufferedComponentScale_pos E hW z
    positivity
  obtain ⟨S,hS,hcover,henlarge,hcount⟩ := planarGrid_finite_cover_of_enlargement_area
    o hδ hB ((measure_mono hsub).trans hbig)
  exact ⟨S,hS,hcover,henlarge.trans hsub,hcount⟩

theorem published_uniform_bufferedComponent_label_packing
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hMono : PublishedOneVariableMonotonicity)
    (s D : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Set (EuclideanSpace ℝ (Fin 2)))
      (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) →
      IsOpen E → Bornology.IsBounded E → ∀ δ W : ℝ,
      0 < δ → 0 < W → c*δ ≤ W → ∀ (z : EuclideanSpace ℝ (Fin 2))
      (ι : Type*) (J : Finset ι) (p : ι → EuclideanSpace ℝ (Fin 2)),
      (∀ i ∈ J, p i ∈ bufferedBandComponent E W z) → ∀ M : ℝ, 0 ≤ M →
      (∀ u : Fin 2 → ℝ, ((J.filter (fun i => p i ∈ planarSquare u δ)).card : ℝ) ≤ M) →
      (J.card : ℝ) ≤ K*M*bufferedComponentScale E W z*W/δ^2 := by
  obtain ⟨K,hK,hgrid⟩ := published_uniform_bufferedComponent_grid_cover
    hCAD hCell hHardt hQE hMono s D
  refine ⟨K*(1+2/c+5)*(1+2/c+4),by positivity,?_⟩
  intro E A hAc hAd hA ho hb δ W hδ hW hwidth z ι J p hp M hM hlocal
  obtain ⟨S,_,hcover,_,hcount⟩ := hgrid E A hAc hAd hA ho hb 1 c δ W
    (by norm_num) hc hδ hW hwidth z 0
  have hpcover (i : ι) (hi : i ∈ J) : p i ∈ ⋃ k ∈ S, planarGridCell 0 δ k :=
    hcover (closure_subset_cthickening (1*W) (bufferedBandComponent E W z) (subset_closure (hp i hi)))
  have hlabels := planarGrid_label_card_bound J p 0 hδ S hpcover
    (fun k => hlocal (fun j => (0 : Fin 2 → ℝ) j+(k j : ℝ)*δ))
  calc
    (J.card : ℝ) ≤ (S.card : ℝ)*M := hlabels
    _ ≤ (K*(1+2/c+5)*(1+2/c+4)*bufferedComponentScale E W z*W/δ^2)*M :=
      mul_le_mul_of_nonneg_right hcount hM
    _ = _ := by ring

theorem published_uniform_bufferedComponent_polynomial_label_packing
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hMono : PublishedOneVariableMonotonicity)
    (s D : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Set (EuclideanSpace ℝ (Fin 2)))
      (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) →
      IsOpen E → Bornology.IsBounded E → ∀ (P Λ W : ℝ) (q r : ℕ),
      0 < P → 0 ≤ Λ → 0 < W → c*(P^q)⁻¹ ≤ W →
      ∀ (z : EuclideanSpace ℝ (Fin 2)) (ι : Type*) (J : Finset ι)
        (p : ι → EuclideanSpace ℝ (Fin 2)),
      (∀ i ∈ J, p i ∈ bufferedBandComponent E W z) →
      (∀ u : Fin 2 → ℝ, ((J.filter (fun i => p i ∈ planarSquare u (P^q)⁻¹)).card : ℝ) ≤ P^r*Λ) →
      (J.card : ℝ) ≤ K*Λ*P^(r+2*q)*bufferedComponentScale E W z*W := by
  obtain ⟨K,hK,hpack⟩ := published_uniform_bufferedComponent_label_packing
    hCAD hCell hHardt hQE hMono s D c hc
  refine ⟨K,hK,?_⟩
  intro E A hAc hAd hA ho hb P Λ W q r hP hΛ hW hwidth z ι J p hp hlocal
  have h := hpack E A hAc hAd hA ho hb (P^q)⁻¹ W (by positivity) hW hwidth
    z ι J p hp (P^r*Λ) (by positivity) hlocal
  convert h using 1
  rw [pow_add,mul_comm 2 q,pow_mul]
  simp only [inv_pow,div_inv_eq_mul]
  ring

end PaperI
