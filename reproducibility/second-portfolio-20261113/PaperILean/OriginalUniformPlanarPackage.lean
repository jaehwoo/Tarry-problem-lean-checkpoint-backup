import PaperILean.OriginalDyadicPackingApplication

/-! I1243-I1265: one joint ORIGINAL component/strip package, with the separately
recorded small-T count correction. Constants precede all Boolean tables, real
coefficients, scales, Borel substitutions and labels. The manuscript is fixed.
-/
noncomputable section
namespace PaperI
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

def originalUniversalPlanarAtoms (s d : ℕ) :
    Finset (MvPolynomial ((Fin s × (Fin 2 → Fin (d+1))) ⊕ Fin 2) ℝ) :=
  Finset.univ.image (universalCoefficientPolynomial (Fin 2) s d)

def originalUniversalPlanarDegree (s d : ℕ) : ℕ :=
  (originalUniversalPlanarAtoms s d).sup MvPolynomial.totalDegree

theorem originalUniversalPlanar_fiber_format (s d : ℕ)
    (b : (Fin s → Bool × Bool) → Bool) (p : (Fin s × (Fin 2 → Fin (d+1))) → ℝ) :
    ∃ A : Finset (MvPolynomial (Fin 2) ℝ), A.card≤s ∧
      (∀ f∈A, f.totalDegree≤originalUniversalPlanarDegree s d) ∧
      PolynomialSignDetermined A (projectionFiber (universalPolynomialBooleanSet (Fin 2) s d b) p) := by
  apply projectionFiber_has_bounded_sign_format p (originalUniversalPlanarAtoms s d)
    (universalPolynomialBooleanSet (Fin 2) s d b) s (originalUniversalPlanarDegree s d)
  · simpa only [originalUniversalPlanarAtoms,Finset.card_univ,Fintype.card_fin] using
      (Finset.card_image_le : (Finset.univ.image (universalCoefficientPolynomial (Fin 2) s d)).card≤(Finset.univ : Finset (Fin s)).card)
  · intro f hf
    exact Finset.le_sup hf
  · intro x y hxy
    change b (polynomialFamilySignCode (universalCoefficientPolynomial (Fin 2) s d) x)=true ↔
      b (polynomialFamilySignCode (universalCoefficientPolynomial (Fin 2) s d) y)=true
    have hcode := (polynomialFamilySignCode_eq_iff
      (universalCoefficientPolynomial (Fin 2) s d) x y).mpr
      (fun i => hxy _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
    rw [hcode]

theorem original_square_density_nonnegative {ι : Type*}
    (active : ι → Prop) (point : ι → EuclideanSpace ℝ (Fin 2))
    (δ P r mass : ℝ) (hP : 0<P)
    (hlocal : ∀ u : Fin 2 → ℝ,
      ({j | active j ∧ point j∈planarSquare u δ}.ncard : ℝ)≤P^r*mass) : 0≤mass := by
  have hprod : 0≤P^r*mass := (Nat.cast_nonneg _).trans (hlocal 0)
  exact nonneg_of_mul_nonneg_right hprod (Real.rpow_pos_of_pos hP r)

theorem original_planar_assignment_exists_unique {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (j : Λ)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E) (hT : 0≤radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox (radius ω))
    {δ : ℝ} (hδ : 0<δ)
    (hbuffer : δ≤Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ)
    (ha : active ω j) :
    ∃! q : ℤ × Fin D.count,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2 := by
  let z := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)
  have hr : 0<Metric.infDist z Eᶜ := hδ.trans_le hbuffer
  have hz : z∈E := Metric.ball_infDist_compl_subset (x := z)
    (by simpa only [Metric.mem_ball,dist_self] using hr)
  exact originalDyadicComponentAssigned_exists_unique D active param radius point ω j
    ho hT hE hbox z hz (by simp [z]) ha hr

def OriginalDyadicPackingBounds {Ω Λ ρ : Type*} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (m : ℕ) (P mass : ℝ) : Prop :=
  (∀ j, active ω j → ∃! q : ℤ × Fin D.count,
    originalDyadicComponentAssigned D active param radius point ω j q.1 q.2) ∧
    Finite {a : ℤ × Fin D.count // ∃ j, originalDyadicComponentAssigned D active param radius point ω j a.1 a.2} ∧
    (Nat.card {a : ℤ × Fin D.count // ∃ j, originalDyadicComponentAssigned D active param radius point ω j a.1 a.2} : ℝ)
      ≤P^m*(planarLogSize (radius ω))^m ∧
    ∀ (k : ℤ) (i : Fin D.count),
      let p := (originalDyadicPositiveParameters param radius k ω).val
      let L := roundedDyadicScale (originalJointComponentScale D i p)
      let W := roundedDyadicScale ((2:ℝ)^k)
      {j | originalDyadicComponentAssigned D active param radius point ω j k i}.Finite ∧
        ({j | originalDyadicComponentAssigned D active param radius point ω j k i}.ncard : ℝ)≤P^m*mass*L*W ∧
        Metric.diam ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' projectionFiber (D.part i) p)≤L ∧
        Metric.diam ((fun j => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) ''
          {j | originalDyadicComponentAssigned D active param radius point ω j k i})≤L

universe u v

theorem published_inputFormat_original_planar_strip_package
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    (hMono : PublishedOneVariableMonotonicity) (s d N : ℕ) (c r : ℝ) :
    ∃ Nc H K m : ℕ, 2≤H ∧ 0<K ∧ 0<m ∧ ∃ C : ℝ, 1≤C ∧
      ∀ b : (Fin s → Bool × Bool) → Bool,
      ∃ D : JointComponentPartition (planarBoundedBandFamily (universalPolynomialBooleanSet (Fin 2) s d b)),
        D.count≤Nc ∧
        ∃ B : Fin D.count → OriginalBorelStripFamily
          (originalJointPositiveWidthDomain (Fin s × (Fin 2 → Fin (d+1)))),
        (∀ (i : Fin D.count) p, (projectionFiber (D.part i) p.val).Nonempty →
          (B i).ComponentStripAt D i H K N C p ∧
          ∀ P : ℝ, 2≤P → P^(-c)/2≤p.val (Sum.inr ()) → (B i).RoundedComponentAt D i N (P^m) p) ∧
        ∀ (Ω : Type u) (Λ : Type v) (active : Ω → Λ → Prop)
          (param : Ω → (Fin s × (Fin 2 → Fin (d+1))) → ℝ) (radius : Ω → ℝ)
          (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω)
          (E : Set (WithLp 2 (Fin 2 → ℝ))),
          IsOpen E → Bornology.IsBounded E → 0≤radius ω →
          (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=projectionFiber (universalPolynomialBooleanSet (Fin 2) s d b) (param ω) →
          (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox (radius ω) →
          ∀ P mass : ℝ, 2≤P →
          (∀ j, active ω j → P^(-c)≤Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ) →
          (∀ u : Fin 2 → ℝ,
            {j | active ω j ∧ (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)∈planarSquare u (P^(-c))}.Finite ∧
            ({j | active ω j ∧ (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)∈planarSquare u (P^(-c))}.ncard : ℝ)≤P^r*mass) →
          OriginalDyadicPackingBounds D active param radius point ω m P mass := by
  classical
  obtain ⟨Nc,H,K,hH,hK,C,hC,hstrips⟩ :=
    published_inputFormat_original_common_strips hDD hCAD hCell hHardt hQE hPiece s d N
  obtain ⟨npack,hpack⟩ := published_originalDyadicAssigned_real_packing
    hCAD hCell.toFiniteConnectedCover hHardt.toHardtTriviality hQE hMono s (originalUniversalPlanarDegree s d) c r
  obtain ⟨ncount,_,hcount⟩ := originalDyadicComponentAssigned_repaired_count.{u,v,0} c Nc
  obtain ⟨a,m,hmin,hmpos,hpowers⟩ := original_uniform_strip_rounding_powers H K N (npack+ncount) C c hH hK hC
  have hpm : npack≤m := (Nat.le_add_right npack ncount).trans hmin
  have hcm : ncount≤m := (Nat.le_add_left ncount npack).trans hmin
  refine ⟨Nc,H,K,m,hH,hK,hmpos,C,hC,?_⟩
  intro b
  obtain ⟨D,hD,hB⟩ := hstrips b
  choose B hB using hB
  refine ⟨D,hD,B,?_,?_⟩
  · intro i p hp
    refine ⟨hB i p hp,?_⟩
    intro P hP hwidth
    rcases hpowers P hP with ⟨hcQ,hdQ,hpiQ,hcomp⟩
    have hs := hcomp (p.val (Sum.inr ())) (originalJointComponentScale D i p.val) hwidth (le_max_left _ _)
    exact (hB i p hp).rounded_of_comparisons hH hK hC (one_le_pow₀ (by linarith : 1≤P)) hs.2 hs.1 hcQ hdQ hpiQ
  · intro Ω Λ active param radius point ω E ho hb hT hE hbox P mass hP hbuffer hlocal
    have hP1 : 1≤P := by linarith
    have hP0 : 0<P := by linarith
    have hmass := original_square_density_nonnegative (active ω)
      (fun j => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) (P^(-c)) P r mass hP0
      (fun u => (hlocal u).2)
    obtain ⟨hfinite,hcard⟩ := hcount D hD active param radius point ω E ho hT hE hbox P hP hbuffer
    refine ⟨?_,hfinite,original_count_enlarge_power hP1 hcm hcard,?_⟩
    · intro j hj
      exact original_planar_assignment_exists_unique D active param radius point ω j ho hT hE hbox
        (Real.rpow_pos_of_pos hP0 (-c)) (hbuffer j hj) hj
    intro k i
    obtain ⟨A,hAc,hAd,hA⟩ := originalUniversalPlanar_fiber_format s d b (param ω)
    rw [← hE] at hA
    obtain ⟨hI,hIcard⟩ := hpack D active param radius point ω E A hAc hAd hA ho hb hT hE hbox P mass hP hmass hbuffer hlocal k i
    refine ⟨hI,hIcard.trans ?_,?_,?_⟩
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP1 hpm) hmass)
          (roundedDyadicScale_pos _).le) (roundedDyadicScale_pos _).le
    · exact (le_max_right _ _).trans (le_roundedDyadicScale _)
    · exact (originalDyadicAssigned_piece_diameter D active param radius point ω k i).trans (le_roundedDyadicScale _)

theorem original_planar_assignment_measurable
    (hQE : PublishedRealSemialgebraicity) {Ω Λ : Type*} [MeasurableSpace Ω]
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (hG : HasPolynomialSignDescription G)
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (B : OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ)
    (ha : ∀ j, MeasurableSet {ω | active ω j}) (hp : Measurable param)
    (hT : Measurable radius) (hx : ∀ j, Measurable (fun ω => point ω j)) (j : Λ) (k : ℤ) :
    MeasurableSet {ω | originalDyadicComponentAssigned D active param radius point ω j k i} ∧
      Measurable (fun ω => (roundedDyadicScale (originalJointComponentScale D i
        (originalDyadicPositiveParameters param radius k ω).val),roundedDyadicScale ((2:ℝ)^k))) ∧
      MeasurableSet {v : Ω × WithLp 2 (Fin 2 → ℝ) |
        v.2∈B.strip (originalDyadicPositiveParameters param radius k v.1) ((2:ℝ)^k)} :=
  ⟨measurableSet_originalDyadicComponentAssigned hQE (hasPolynomialSignDescription_definable hG)
      D active param radius point ha hp hT hx j k i,
    published_originalDyadicComponentScales_measurable hQE D param radius hp hT k i,
    originalDyadicCommonStrip_measurable B param radius k hp hT⟩

end PaperI
