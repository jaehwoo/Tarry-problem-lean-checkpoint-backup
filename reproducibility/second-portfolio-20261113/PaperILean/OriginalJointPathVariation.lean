import PaperILean.OriginalJointPathSelection
import PaperILean.BoundedPathOriginalVariation
import PaperILean.CoordinatePathFormat

/-! Original analytic/actual derivative-sign subdivision of the SAME jointly
selected path. Constants precede the coefficient/radius/width valuation and
labels. Their dependence here is on the fixed joint catalogue and graph
budgets; ambient input-format-only specialization is a separate obligation. -/
noncomputable section
namespace PaperI
open Set

/-- Records the actual finite cuts and monotone partition, not only a bound
deduced from an unspecified replacement curve. No Borel choice of cuts is
part of this proposition. -/
def OriginalCoordinateSubdivisionVariation {κ : Type*} [Fintype κ]
    (g : ℝ → κ → ℝ) (K M : ℕ) (B : ℝ) : Prop :=
  ∃ cuts : Finset ℝ, 0 ∈ cuts ∧ 1 ∈ cuts ∧
    (∀ c ∈ cuts, c ∈ Icc (0 : ℝ) 1) ∧ cuts.card ≤ K ∧
    (∀ u ∈ cuts, ∀ v ∈ cuts, u < v → (∀ c ∈ cuts, c ∉ Ioo u v) →
      ∀ i, AnalyticOnNhd ℝ (fun r => g r i) (Ioo u v) ∧
        DerivativeSignOn (fun r => g r i) (Ioo u v)) ∧
    ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ M ∧ t 0 = 0 ∧ t n = 1 ∧
      MonotoneOn t (Icc 0 n) ∧
      (∀ j < n, ∀ i, MonotoneOn (fun r => g r i) (Ioo (t j) (t (j+1))) ∨
        AntitoneOn (fun r => g r i) (Ioo (t j) (t (j+1)))) ∧
      (∀ i, BoundedVariationOn (fun r => g r i) (Icc (0 : ℝ) 1) ∧
        variationOnFromTo (fun r => g r i) univ 0 1 ≤ (M : ℝ)*B) ∧
      (∑ i, variationOnFromTo (fun r => g r i) univ 0 1) ≤
        (Fintype.card κ : ℝ)*M*B

/-- Uniform for every already supplied path with the displayed graph format.
This theorem never chooses a different endpoint path. -/
theorem published_bounded_path_coordinate_original_variation
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    (d sS dS sPath dPath : ℕ) :
    ∃ K M : ℕ, ∀ (A : Finset (MvPolynomial (Fin d) ℝ)) (S : Set (Fin d → ℝ)),
      A.card ≤ sS → (∀ q ∈ A, q.totalDegree ≤ dS) → PolynomialSignDetermined A S →
      Bornology.IsBounded ((WithLp.equiv 2 (Fin d → ℝ)).symm '' S) →
      ∀ (a b : Fin d → ℝ) (γ : SemialgebraicUnitPath S a b)
        (P : Finset (MvPolynomial (Unit ⊕ Fin d) ℝ)),
      P.card ≤ sPath → (∀ q ∈ P, q.totalDegree ≤ dPath) →
      PolynomialSignDetermined P (unitPathGraph γ.toFun) →
      OriginalCoordinateSubdivisionVariation γ.toFun K M
        (Metric.diam ((WithLp.equiv 2 (Fin d → ℝ)).symm '' S)) := by
  obtain ⟨K,M,h⟩ := published_bounded_unitPath_original_partition_variation
    hCell hHardt hQE hNash hPiece (Fin d) (Fin d) sPath dPath (sS+1) (max dS 1)
  refine ⟨K,M,?_⟩
  intro A S hAcard hAdeg hA hbdd a b γ P hPcard hPdeg hP
  obtain ⟨cuts,h0,h1,hI,hK,hcuts,n,t,hn,ht0,ht1,ht,hm,hv⟩ :=
    h S a b γ P hPcard hPdeg hP (fun i x => x i)
      (fun _ => Metric.diam ((WithLp.equiv 2 (Fin d → ℝ)).symm '' S))
      (fun i => (continuous_apply i).continuousOn)
      (coordinate_graph_bounded_sign_format A S sS dS hAcard hAdeg hA)
      (coordinate_range_le_euclidean_diameter S hbdd)
  refine ⟨cuts,h0,h1,hI,hK,hcuts,n,t,hn,ht0,ht1,ht,hm,hv,?_⟩
  calc
    (∑ i, variationOnFromTo (fun r => γ.toFun r i) univ 0 1) ≤
        ∑ _i : Fin d, (M : ℝ)*Metric.diam ((WithLp.equiv 2 (Fin d → ℝ)).symm '' S) :=
      Finset.sum_le_sum (fun i _ => (hv i).2)
    _ = (Fintype.card (Fin d) : ℝ)*M*
        Metric.diam ((WithLp.equiv 2 (Fin d → ℝ)).symm '' S) := by simp [mul_assoc]

/-- The same constants apply to every valuation and every supplied path of
the given format in this catalogue entry. On the exact large branch L0 is
the Euclidean diameter, with no extra factor or lower radius restriction. -/
theorem published_originalJointPath_variation
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (sPath dPath : ℕ) :
    ∃ K M : ℕ, ∀ (p : originalJointLargeComponentDomain D i) (a b : Fin 2 → ℝ)
      (γ : SemialgebraicUnitPath (projectionFiber (D.part i) p.val) a b)
      (P : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ)),
      P.card ≤ sPath → (∀ q ∈ P, q.totalDegree ≤ dPath) →
      PolynomialSignDetermined P (unitPathGraph γ.toFun) →
      OriginalCoordinateSubdivisionVariation γ.toFun K M (originalJointComponentScale D i p.val) := by
  obtain ⟨sS,dS,hS⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format (D.semialgebraic i)
  obtain ⟨K,M,h⟩ := published_bounded_path_coordinate_original_variation
    hCell hHardt hQE hNash hPiece 2 sS dS sPath dPath
  refine ⟨K,M,?_⟩
  intro p a b γ P hPcard hPdeg hP
  obtain ⟨A,hAcard,hAdeg,hA⟩ := hS p.val
  rw [originalJointLargeComponentScale_eq_diameter D i p.property]
  exact h A _ hAcard hAdeg hA (originalJointBand_part_euclidean_isBounded D p.val i)
    a b γ P hPcard hPdeg hP

/-- Joint selection and original subdivision for one fixed catalogue entry.
The selected map g, not a pointwise replacement, carries every certificate. -/
theorem published_originalJointLargePaths_with_original_variation
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count) :
    ∃ (s d K M : ℕ) (a b : originalJointLargeComponentDomain D i → Fin 2 → ℝ)
      (g : originalJointLargeComponentDomain D i → ℝ → Fin 2 → ℝ),
      Measurable a ∧ Measurable b ∧
      Measurable (fun v : originalJointLargeComponentDomain D i × Icc (0 : ℝ) 1 =>
        g v.1 v.2.val) ∧
      MeasurableSet {v : (originalJointLargeComponentDomain D i × Icc (0 : ℝ) 1) ×
        (Fin 2 → ℝ) | g v.1.1 v.1.2.val = v.2} ∧
      (∀ p, a p ∈ projectionFiber (D.part i) p.val ∧
        b p ∈ projectionFiber (D.part i) p.val ∧ a p ≠ b p ∧
        originalJointComponentScale D i p.val / 2 <
          dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (a p))
            ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (b p)) ∧
        dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (a p))
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (b p)) ≤ originalJointComponentScale D i p.val) ∧
      (∀ p, ∃ γ : SemialgebraicUnitPath (projectionFiber (D.part i) p.val) (a p) (b p),
        γ.toFun = g p ∧ ∃ A : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ),
          A.card ≤ s ∧ (∀ q ∈ A, q.totalDegree ≤ d) ∧
          PolynomialSignDetermined A (unitPathGraph γ.toFun)) ∧
      ∀ p, OriginalCoordinateSubdivisionVariation (g p) K M
        (originalJointComponentScale D i p.val) := by
  obtain ⟨s,d,a,b,g,ha,hb,hg,hgraph,hend,hpaths⟩ :=
    published_originalJointLargePaths hCAD hQE hHardt.toHardtTriviality D i
  obtain ⟨K,M,hvar⟩ := published_originalJointPath_variation hCell hHardt hQE hNash hPiece D i s d
  refine ⟨s,d,K,M,a,b,g,ha,hb,hg,hgraph,hend,hpaths,?_⟩
  intro p
  obtain ⟨γ,hγ,A,hcard,hdeg,hA⟩ := hpaths p
  rw [← hγ]
  exact hvar p (a p) (b p) γ A hcard hdeg hA

theorem OriginalCoordinateSubdivisionVariation.mono {κ : Type*} [Fintype κ]
    {g : ℝ → κ → ℝ} {K M K' M' : ℕ} {B : ℝ}
    (h : OriginalCoordinateSubdivisionVariation g K M B)
    (hK : K ≤ K') (hM : M ≤ M') (hB : 0 ≤ B) :
    OriginalCoordinateSubdivisionVariation g K' M' B := by
  obtain ⟨cuts,h0,h1,hI,hcard,hcuts,n,t,hn,ht0,ht1,ht,hm,hv,hsum⟩ := h
  have hM' : (M : ℝ) ≤ M' := by exact_mod_cast hM
  refine ⟨cuts,h0,h1,hI,hcard.trans hK,hcuts,n,t,hn.trans hM,ht0,ht1,ht,hm,?_,?_⟩
  · exact fun i => ⟨(hv i).1,(hv i).2.trans (mul_le_mul_of_nonneg_right hM' hB)⟩
  · exact hsum.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hM' (by positivity)) hB)

/-- Finite maxima remove dependence on the catalogue entry as well as on
the coefficient valuation and chosen endpoints. The empty catalogue is
included; there is no positive-count assumption. -/
theorem published_originalJointLargePaths_for_endpoints_uniform_catalogue
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) :
    ∃ s d : ℕ, ∀ (i : Fin D.count)
      (a b : originalJointLargeComponentDomain D i → Fin 2 → ℝ),
      Measurable a → Measurable b →
      (∀ p, a p ∈ projectionFiber (D.part i) p.val) →
      (∀ p, b p ∈ projectionFiber (D.part i) p.val) →
      ∃ g : originalJointLargeComponentDomain D i → ℝ → Fin 2 → ℝ,
        Measurable (fun v : originalJointLargeComponentDomain D i × Icc (0 : ℝ) 1 =>
          g v.1 v.2.val) ∧
        ∀ p, ∃ γ : SemialgebraicUnitPath (projectionFiber (D.part i) p.val) (a p) (b p),
          γ.toFun = g p ∧ ∃ A : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ),
            A.card ≤ s ∧ (∀ q ∈ A, q.totalDegree ≤ d) ∧
            PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  classical
  choose s d h using fun i => published_originalJointLargePaths_for_endpoints hCAD hQE hHardt D i
  refine ⟨Finset.univ.sup s,Finset.univ.sup d,?_⟩
  intro i a b ha hb haS hbS
  obtain ⟨g,hg,hpath⟩ := h i a b ha hb haS hbS
  refine ⟨g,hg,?_⟩
  intro p
  obtain ⟨γ,hγ,A,hcard,hdeg,hA⟩ := hpath p
  exact ⟨γ,hγ,A,hcard.trans (Finset.le_sup (f := s) (Finset.mem_univ i)),
    fun q hq => (hdeg q hq).trans (Finset.le_sup (f := d) (Finset.mem_univ i)),hA⟩

theorem published_originalJointPath_variation_uniform_catalogue
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (sPath dPath : ℕ) :
    ∃ K M : ℕ, ∀ (i : Fin D.count) (p : originalJointLargeComponentDomain D i)
      (a b : Fin 2 → ℝ)
      (γ : SemialgebraicUnitPath (projectionFiber (D.part i) p.val) a b)
      (P : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ)),
      P.card ≤ sPath → (∀ q ∈ P, q.totalDegree ≤ dPath) →
      PolynomialSignDetermined P (unitPathGraph γ.toFun) →
      OriginalCoordinateSubdivisionVariation γ.toFun K M (originalJointComponentScale D i p.val) := by
  classical
  choose K M h using fun i =>
    published_originalJointPath_variation hCell hHardt hQE hNash hPiece D i sPath dPath
  refine ⟨Finset.univ.sup K,Finset.univ.sup M,?_⟩
  intro i p a b γ P hcard hdeg hP
  exact (h i p a b γ P hcard hdeg hP).mono
    (Finset.le_sup (f := K) (Finset.mem_univ i))
    (Finset.le_sup (f := M) (Finset.mem_univ i))
    (originalJointComponentScale_nonneg D i p.val)

/-- One common format/variation budget precedes EVERY entry, coefficient,
radius, width and label of the supplied fixed joint catalogue. -/
theorem published_originalJointLargePaths_uniform_catalogue
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) :
    ∃ s d K M : ℕ, ∀ i : Fin D.count,
      ∃ (a b : originalJointLargeComponentDomain D i → Fin 2 → ℝ)
        (g : originalJointLargeComponentDomain D i → ℝ → Fin 2 → ℝ),
        Measurable a ∧ Measurable b ∧
        Measurable (fun v : originalJointLargeComponentDomain D i × Icc (0 : ℝ) 1 =>
          g v.1 v.2.val) ∧
        MeasurableSet {v : (originalJointLargeComponentDomain D i × Icc (0 : ℝ) 1) ×
          (Fin 2 → ℝ) | g v.1.1 v.1.2.val = v.2} ∧
        (∀ p, a p ∈ projectionFiber (D.part i) p.val ∧
          b p ∈ projectionFiber (D.part i) p.val ∧ a p ≠ b p ∧
          originalJointComponentScale D i p.val / 2 <
            dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (a p))
              ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (b p)) ∧
          dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (a p))
            ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (b p)) ≤ originalJointComponentScale D i p.val) ∧
        (∀ p, ∃ γ : SemialgebraicUnitPath (projectionFiber (D.part i) p.val) (a p) (b p),
          γ.toFun = g p ∧ ∃ A : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ),
            A.card ≤ s ∧ (∀ q ∈ A, q.totalDegree ≤ d) ∧
            PolynomialSignDetermined A (unitPathGraph γ.toFun)) ∧
        ∀ p, OriginalCoordinateSubdivisionVariation (g p) K M
          (originalJointComponentScale D i p.val) := by
  obtain ⟨s,d,hpaths⟩ := published_originalJointLargePaths_for_endpoints_uniform_catalogue
    hCAD hQE hHardt.toHardtTriviality D
  obtain ⟨K,M,hvar⟩ := published_originalJointPath_variation_uniform_catalogue
    hCell hHardt hQE hNash hPiece D s d
  refine ⟨s,d,K,M,?_⟩
  intro i
  obtain ⟨a,b,ha,hb,_,hend⟩ := published_originalJointLargeEndpoints hCAD hQE hHardt.toHardtTriviality D i
  obtain ⟨g,hg,hpath⟩ := hpaths i a b ha hb (fun p => (hend p).1) (fun p => (hend p).2.1)
  refine ⟨a,b,g,ha,hb,hg,jointRestrictedPath_graph_measurable g hg,hend,hpath,?_⟩
  intro p
  obtain ⟨γ,hγ,A,hcard,hdeg,hA⟩ := hpath p
  rw [← hγ]
  exact hvar i p (a p) (b p) γ A hcard hdeg hA

end PaperI
