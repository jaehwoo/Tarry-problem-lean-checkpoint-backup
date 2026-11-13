import PaperILean.OriginalCommonStripCatalogue
import PaperILean.OriginalPlanarSmallRadiusRepair
import PaperILean.PolynomialFiberFormat

/-! I1259/I1261: use the original arclength/square packing on the SAME
component and labels. Real exponents and coincident label points are retained.
Local finite cardinality is explicit; ncard alone cannot express it. -/
noncomputable section
namespace PaperI
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

theorem published_uniform_bufferedComponent_mesh_index_packing
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hMono : PublishedOneVariableMonotonicity)
    (s d : ℕ) (c : ℝ) (hc : 0<c) :
    ∃ K : ℝ, 0<K ∧ ∀ (E : Set (EuclideanSpace ℝ (Fin 2)))
      (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card≤s →
      (∀ f∈A, f.totalDegree≤d) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) →
      IsOpen E → Bornology.IsBounded E → ∀ δ W M : ℝ,
      0<δ → 0<W → c*δ≤W → 0≤M →
      ∀ (z : EuclideanSpace ℝ (Fin 2)) (ι : Type*) (I : Set ι)
        (point : ι → EuclideanSpace ℝ (Fin 2)),
      (∀ j∈I, point j∈bufferedBandComponent E W z) →
      (∀ u : Fin 2 → ℝ, {j | j∈I ∧ point j∈planarSquare u δ}.Finite ∧
        ({j | j∈I ∧ point j∈planarSquare u δ}.ncard : ℝ)≤M) →
      I.Finite ∧ (I.ncard : ℝ)≤K*M*bufferedComponentScale E W z*W/δ^2 := by
  obtain ⟨K,hK,hpack⟩ := published_uniform_bufferedComponent_label_packing
    hCAD hCell hHardt hQE hMono s d c hc
  refine ⟨K,hK,?_⟩
  intro E A hAc hAd hA ho hb δ W M hδ hW hwidth hM z ι I point hp hlocal
  have hbound (J : Finset ι) (hJ : (J : Set ι)⊆I) :
      (J.card : ℝ)≤K*M*bufferedComponentScale E W z*W/δ^2 :=
    hpack E A hAc hAd hA ho hb δ W hδ hW hwidth z ι J point
      (fun j hj => hp j (hJ hj)) M hM (finite_subfamily_square_card_bound point hlocal J hJ)
  have hI := finite_set_of_uniform_finset_card_bound I _ hbound
  refine ⟨hI,?_⟩
  rw [Set.ncard_eq_toFinset_card I hI]
  exact hbound hI.toFinset (fun _ hj => hI.mem_toFinset.mp hj)

theorem original_real_mesh_inverse_square_bound (c : ℝ) :
    ∃ q : ℕ, ∀ P : ℝ, 2≤P → ((P^(-c))^2)⁻¹≤P^(2*q) := by
  obtain ⟨q,hq⟩ := original_inverse_real_power_minorant c
  refine ⟨q,?_⟩
  intro P hP
  have hP0 : 0<P := by linarith
  have hδ : 0<P^(-c) := Real.rpow_pos_of_pos hP0 _
  have hinv : (P^(-c))⁻¹≤P^q := by
    have h := one_div_le_one_div_of_le (by positivity : 0<(P^q)⁻¹) (hq P hP)
    simpa only [one_div,inv_inv] using h
  rw [show 2*q=q*2 by omega,pow_mul]
  simpa only [inv_pow] using pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hinv 2

theorem published_uniform_bufferedComponent_real_power_packing
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hMono : PublishedOneVariableMonotonicity)
    (s d : ℕ) (c r : ℝ) :
    ∃ m : ℕ, ∀ (E : Set (EuclideanSpace ℝ (Fin 2)))
      (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card≤s →
      (∀ f∈A, f.totalDegree≤d) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) →
      IsOpen E → Bornology.IsBounded E → ∀ P Λ W : ℝ,
      2≤P → 0≤Λ → 0<W → P^(-c)/2≤W →
      ∀ (z : EuclideanSpace ℝ (Fin 2)) (ι : Type*) (I : Set ι)
        (point : ι → EuclideanSpace ℝ (Fin 2)),
      (∀ j∈I, point j∈bufferedBandComponent E W z) →
      (∀ u : Fin 2 → ℝ, {j | j∈I ∧ point j∈planarSquare u (P^(-c))}.Finite ∧
        ({j | j∈I ∧ point j∈planarSquare u (P^(-c))}.ncard : ℝ)≤P^r*Λ) →
      I.Finite ∧ (I.ncard : ℝ)≤P^m*Λ*bufferedComponentScale E W z*W := by
  obtain ⟨K,hK,hpack⟩ := published_uniform_bufferedComponent_mesh_index_packing
    hCAD hCell hHardt hQE hMono s d (1/2) (by norm_num)
  obtain ⟨n,hn⟩ := uniform_constant_le_power K
  obtain ⟨q,hq⟩ := original_real_mesh_inverse_square_bound c
  obtain ⟨t,ht⟩ := exists_nat_ge r
  refine ⟨n+t+2*q,?_⟩
  intro E A hAc hAd hA ho hb P Λ W hP hΛ hW hwidth z ι I point hp hlocal
  have hP0 : 0<P := by linarith
  have hδ : 0<P^(-c) := Real.rpow_pos_of_pos hP0 _
  obtain ⟨hI,hbound⟩ := hpack E A hAc hAd hA ho hb (P^(-c)) W (P^r*Λ)
    hδ hW (by linarith) (mul_nonneg (Real.rpow_nonneg hP0.le _) hΛ) z ι I point hp hlocal
  have hr : P^r≤P^t := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤P) ht
  have hL : 0≤bufferedComponentScale E W z := (bufferedComponentScale_pos E hW z).le
  refine ⟨hI,hbound.trans ?_⟩
  calc
    K*(P^r*Λ)*bufferedComponentScale E W z*W/(P^(-c))^2
        = K*P^r*((P^(-c))^2)⁻¹*Λ*bufferedComponentScale E W z*W := by ring
    _ ≤ P^n*P^t*P^(2*q)*Λ*bufferedComponentScale E W z*W := by
      gcongr <;> first | exact hn P hP | exact hr | exact hq P hP
    _ = _ := by rw [pow_add,pow_add]

theorem originalDyadicComponentAssigned_width_lower
    {Ω Λ ρ : Type*} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) {ω : Ω} {j : Λ} {k : ℤ} {i : Fin D.count}
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E) (hT : 0≤radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox (radius ω))
    {δ : ℝ} (hbuffer : δ≤Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ)
    (hj : originalDyadicComponentAssigned D active param radius point ω j k i) :
    δ/2<(2:ℝ)^k := by
  have hcore : (WithLp.equiv 2 (Fin 2 → ℝ))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j))∈
      planarBoundedCore ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) (radius ω) ((2:ℝ)^k) := by
    simpa only [Equiv.apply_symm_apply,hE] using hj.1.2
  rw [planarBoundedCore_coordinates_iff hT ho hbox] at hcore
  exact dyadic_core_buffer_lower hbuffer hcore.2.2

theorem originalDyadicComponentAssigned_same_component
    {Ω Λ ρ : Type*} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) {ω : Ω} {j j' : Λ} {k : ℤ} {i : Fin D.count}
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E) (hT : 0≤radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox (radius ω))
    (hj : originalDyadicComponentAssigned D active param radius point ω j k i)
    (hj' : originalDyadicComponentAssigned D active param radius point ω j' k i) :
    (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j')∈
      bufferedBandComponent E ((2:ℝ)^k) ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) := by
  apply originalDyadicComponentAssigned_endpoint_mem D active param radius point ho hT hE hbox
    ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) (by simp) hj
  exact hj'.2

theorem originalDyadicAssigned_piece_diameter
    {Ω Λ ρ : Type*} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (k : ℤ) (i : Fin D.count) :
    Metric.diam ((fun j => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) ''
      {j | originalDyadicComponentAssigned D active param radius point ω j k i})≤
        originalJointComponentScale D i (originalDyadicPositiveParameters param radius k ω).val := by
  have hsub : ((fun j => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) ''
      {j | originalDyadicComponentAssigned D active param radius point ω j k i})⊆
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm ''
        projectionFiber (D.part i) (originalDyadicPositiveParameters param radius k ω).val := by
    rintro x ⟨j,hj,rfl⟩
    exact ⟨point ω j,hj.2,rfl⟩
  exact (Metric.diam_mono hsub (originalJointBand_part_euclidean_isBounded D _ i)).trans (le_max_right _ _)

end PaperI
