import PaperILean.OriginalRoundedComponentStrip

/-! Apply the original mesh count to the actual dyadic/core component labels.
The local mesh and original predicate are unchanged; no finite label type or
injective point map is introduced. -/
noncomputable section
namespace PaperI
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

theorem original_square_local_packing_subset {ι : Type*} {I J : Set ι}
    (point : ι → EuclideanSpace ℝ (Fin 2)) (δ M : ℝ) (hsub : I⊆J)
    (hlocal : ∀ u : Fin 2 → ℝ, {j | j∈J ∧ point j∈planarSquare u δ}.Finite ∧
      ({j | j∈J ∧ point j∈planarSquare u δ}.ncard : ℝ)≤M) :
    ∀ u : Fin 2 → ℝ, {j | j∈I ∧ point j∈planarSquare u δ}.Finite ∧
      ({j | j∈I ∧ point j∈planarSquare u δ}.ncard : ℝ)≤M := by
  intro u
  have h : {j | j∈I ∧ point j∈planarSquare u δ}⊆{j | j∈J ∧ point j∈planarSquare u δ} :=
    fun _ hj => ⟨hsub hj.1,hj.2⟩
  exact ⟨(hlocal u).1.subset h,(Nat.cast_le.mpr (Set.ncard_le_ncard h (hlocal u).1)).trans (hlocal u).2⟩

theorem published_originalDyadicAssigned_real_packing
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hMono : PublishedOneVariableMonotonicity)
    (s d : ℕ) (c r : ℝ) :
    ∃ m : ℕ, ∀ {Ω Λ ρ : Type*} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
      (D : JointComponentPartition (planarBoundedBandFamily G))
      (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
      (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω)
      (E : Set (WithLp 2 (Fin 2 → ℝ))) (A : Finset (MvPolynomial (Fin 2) ℝ)),
      A.card≤s → (∀ f∈A, f.totalDegree≤d) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) →
      IsOpen E → Bornology.IsBounded E → 0≤radius ω →
      (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=projectionFiber G (param ω) →
      (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox (radius ω) →
      ∀ P mass : ℝ, 2≤P → 0≤mass →
      (∀ j, active ω j → P^(-c)≤Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ) →
      (∀ u : Fin 2 → ℝ,
        {j | active ω j ∧ (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)∈planarSquare u (P^(-c))}.Finite ∧
        ({j | active ω j ∧ (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)∈planarSquare u (P^(-c))}.ncard : ℝ)≤P^r*mass) →
      ∀ (k : ℤ) (i : Fin D.count),
      {j | originalDyadicComponentAssigned D active param radius point ω j k i}.Finite ∧
        ({j | originalDyadicComponentAssigned D active param radius point ω j k i}.ncard : ℝ)≤
          P^m*mass*roundedDyadicScale (originalJointComponentScale D i
            (originalDyadicPositiveParameters param radius k ω).val)*roundedDyadicScale ((2:ℝ)^k) := by
  obtain ⟨m,hm⟩ := published_uniform_bufferedComponent_real_power_packing
    hCAD hCell hHardt hQE hMono s d c r
  refine ⟨m,?_⟩
  intro Ω Λ ρ G D active param radius point ω E A hAc hAd hA ho hb hT hE hbox P mass hP hmass hbuffer hlocal k i
  have hP0 : 0≤P := by linarith
  let I : Set Λ := {j | originalDyadicComponentAssigned D active param radius point ω j k i}
  let L0 := originalJointComponentScale D i (originalDyadicPositiveParameters param radius k ω).val
  have hL : 0≤L0 := originalJointComponentScale_nonneg D i _
  have hW : 0<(2:ℝ)^k := zpow_pos (by norm_num) k
  by_cases hne : I.Nonempty
  · obtain ⟨j,hj⟩ := hne
    let z := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)
    have hw := originalDyadicComponentAssigned_width_lower D active param radius point ho hT hE hbox
      (hbuffer j hj.1.1) hj
    have hlocalI := original_square_local_packing_subset
      (fun j => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) (P^(-c)) (P^r*mass)
      (show I⊆{j | active ω j} from fun _ hj => hj.1.1) hlocal
    obtain ⟨hI,hbound⟩ := hm E A hAc hAd hA ho hb P mass ((2:ℝ)^k) hP hmass hW hw.le z Λ I
      (fun j => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j))
      (fun j' hj' => originalDyadicComponentAssigned_same_component D active param radius point ho hT hE hbox hj hj') hlocalI
    have hscale := originalDyadicComponentAssigned_scale_eq D active param radius point ho hT hE hbox z
      (by simp [z]) hj
    change L0=bufferedComponentScale E ((2:ℝ)^k) z at hscale
    rw [← hscale] at hbound
    refine ⟨hI,hbound.trans ?_⟩
    exact mul_le_mul (mul_le_mul_of_nonneg_left (le_roundedDyadicScale L0)
      (mul_nonneg (pow_nonneg (by linarith : 0≤P) m) hmass)) (le_roundedDyadicScale _)
      hW.le (mul_nonneg (mul_nonneg (pow_nonneg hP0 m) hmass) (roundedDyadicScale_pos _).le)
  · have hI : I=∅ := not_nonempty_iff_eq_empty.mp hne
    change I.Finite ∧ (I.ncard : ℝ)≤_
    rw [hI,Set.ncard_empty,Nat.cast_zero]
    exact ⟨finite_empty,mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hP0 m) hmass)
      (roundedDyadicScale_pos _).le) (roundedDyadicScale_pos _).le⟩

theorem original_count_enlarge_power {P T count : ℝ} {n m : ℕ}
    (hP : 1≤P) (hnm : n≤m) (hcount : count≤P^n*(planarLogSize T)^n) :
    count≤P^m*(planarLogSize T)^m := by
  exact hcount.trans (mul_le_mul (pow_le_pow_right₀ hP hnm)
    (pow_le_pow_right₀ (planarLogSize_one_le T) hnm)
    (pow_nonneg (planarLogSize_pos T).le n) (pow_nonneg (by linarith) m))

theorem originalDyadicAssigned_rounded_strip
    {Ω Λ : Type*} {ρ : Type} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (B : OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ)) (N m : ℕ) (c : ℝ)
    (hB : ∀ p, (projectionFiber (D.part i) p.val).Nonempty → ∀ P : ℝ, 2≤P →
      P^(-c)/2≤p.val (Sum.inr ()) → B.RoundedComponentAt D i N (P^m) p)
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) {ω : Ω} {j : Λ} {k : ℤ}
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E) (hT : 0≤radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox (radius ω))
    (P : ℝ) (hP : 2≤P)
    (hbuffer : P^(-c)≤Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ)
    (hj : originalDyadicComponentAssigned D active param radius point ω j k i) :
    B.RoundedComponentAt D i N (P^m) (originalDyadicPositiveParameters param radius k ω) :=
  hB _ ⟨point ω j,hj.2⟩ P hP
    (originalDyadicComponentAssigned_width_lower D active param radius point ho hT hE hbox hbuffer hj).le

end PaperI
