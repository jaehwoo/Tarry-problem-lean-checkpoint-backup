import PaperILean.BufferedComponentGridPacking
import Mathlib.Data.Set.Card

/-! I1261: no finite ambient index type or injective point map is assumed.
The manuscript's finite square-local number of indices is expressed by
finiteness AND its cardinal bound (ncard alone would be zero for infinity). -/

noncomputable section
namespace PaperI
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

theorem finite_set_of_uniform_finset_card_bound {ι : Type*} (I : Set ι) (B : ℝ)
    (hbound : ∀ J : Finset ι, (J : Set ι) ⊆ I → (J.card : ℝ) ≤ B) : I.Finite := by
  by_contra hinf
  obtain ⟨N,hN⟩ := exists_nat_gt B
  obtain ⟨J,hJ,hcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
  have h := hbound J hJ
  rw [hcard] at h
  exact (not_le_of_gt hN) h

theorem finite_subfamily_square_card_bound {ι : Type*} {I : Set ι}
    (p : ι → EuclideanSpace ℝ (Fin 2)) {δ M : ℝ}
    (hlocal : ∀ u : Fin 2 → ℝ, {i | i ∈ I ∧ p i ∈ planarSquare u δ}.Finite ∧
      ({i | i ∈ I ∧ p i ∈ planarSquare u δ}.ncard : ℝ) ≤ M)
    (J : Finset ι) (hJ : (J : Set ι) ⊆ I) (u : Fin 2 → ℝ) :
    ((J.filter (fun i => p i ∈ planarSquare u δ)).card : ℝ) ≤ M := by
  have hsub : (↑(J.filter (fun i => p i ∈ planarSquare u δ)) : Set ι) ⊆
      {i | i ∈ I ∧ p i ∈ planarSquare u δ} := by
    intro i hi
    exact ⟨hJ (Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2⟩
  have hn := Set.ncard_le_ncard hsub (hlocal u).1
  rw [Set.ncard_coe_Finset] at hn
  exact (Nat.cast_le.mpr hn).trans (hlocal u).2

theorem published_uniform_bufferedComponent_index_packing
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
      ∀ (z : EuclideanSpace ℝ (Fin 2)) (ι : Type*) (I : Set ι)
        (p : ι → EuclideanSpace ℝ (Fin 2)),
      (∀ i ∈ I, p i ∈ bufferedBandComponent E W z) →
      (∀ u : Fin 2 → ℝ, {i | i ∈ I ∧ p i ∈ planarSquare u (P^q)⁻¹}.Finite ∧
        ({i | i ∈ I ∧ p i ∈ planarSquare u (P^q)⁻¹}.ncard : ℝ) ≤ P^r*Λ) →
      I.Finite ∧ (I.ncard : ℝ) ≤ K*Λ*P^(r+2*q)*bufferedComponentScale E W z*W := by
  obtain ⟨K,hK,hpack⟩ := published_uniform_bufferedComponent_polynomial_label_packing
    hCAD hCell hHardt hQE hMono s D c hc
  refine ⟨K,hK,?_⟩
  intro E A hAc hAd hA ho hb P Λ W q r hP hΛ hW hwidth z ι I p hp hlocal
  have hbound (J : Finset ι) (hJ : (J : Set ι) ⊆ I) :
      (J.card : ℝ) ≤ K*Λ*P^(r+2*q)*bufferedComponentScale E W z*W :=
    hpack E A hAc hAd hA ho hb P Λ W q r hP hΛ hW hwidth z ι J p
      (fun i hi => hp i (hJ hi)) (finite_subfamily_square_card_bound p hlocal J hJ)
  have hI := finite_set_of_uniform_finset_card_bound I _ hbound
  refine ⟨hI,?_⟩
  rw [Set.ncard_eq_toFinset_card I hI]
  exact hbound hI.toFinset (fun _ hi => hI.mem_toFinset.mp hi)

theorem uniform_constant_le_power (K : ℝ) :
    ∃ N : ℕ, ∀ P : ℝ, 2 ≤ P → K ≤ P^N := by
  obtain ⟨N,hN⟩ := exists_nat_ge K
  have htwo : (N : ℝ) ≤ (2 : ℝ)^N := by exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
  exact ⟨N,fun P hP => hN.trans (htwo.trans (pow_le_pow_left₀ (by norm_num) hP N))⟩

theorem published_uniform_bufferedComponent_index_power_packing
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hMono : PublishedOneVariableMonotonicity)
    (s D : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ (E : Set (EuclideanSpace ℝ (Fin 2)))
      (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) →
      IsOpen E → Bornology.IsBounded E → ∀ (P Λ W : ℝ) (q r : ℕ),
      2 ≤ P → 0 ≤ Λ → 0 < W → c*(P^q)⁻¹ ≤ W →
      ∀ (z : EuclideanSpace ℝ (Fin 2)) (ι : Type*) (I : Set ι)
        (p : ι → EuclideanSpace ℝ (Fin 2)),
      (∀ i ∈ I, p i ∈ bufferedBandComponent E W z) →
      (∀ u : Fin 2 → ℝ, {i | i ∈ I ∧ p i ∈ planarSquare u (P^q)⁻¹}.Finite ∧
        ({i | i ∈ I ∧ p i ∈ planarSquare u (P^q)⁻¹}.ncard : ℝ) ≤ P^r*Λ) →
      I.Finite ∧ (I.ncard : ℝ) ≤ P^(N+r+2*q)*Λ*bufferedComponentScale E W z*W := by
  obtain ⟨K,_,hpack⟩ := published_uniform_bufferedComponent_index_packing
    hCAD hCell hHardt hQE hMono s D c hc
  obtain ⟨N,hN⟩ := uniform_constant_le_power K
  refine ⟨N,?_⟩
  intro E A hAc hAd hA ho hb P Λ W q r hP hΛ hW hwidth z ι I p hp hlocal
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hP
  obtain ⟨hIf,hI⟩ := hpack E A hAc hAd hA ho hb P Λ W q r hP0 hΛ hW hwidth
    z ι I p hp hlocal
  refine ⟨hIf,hI.trans ?_⟩
  have hL := bufferedComponentScale_pos E hW z
  calc
    K*Λ*P^(r+2*q)*bufferedComponentScale E W z*W ≤
        P^N*Λ*P^(r+2*q)*bufferedComponentScale E W z*W := by
      gcongr
      exact hN P hP
    _ = _ := by rw [show N+r+2*q=N+(r+2*q) by omega,pow_add]; ring

end PaperI
