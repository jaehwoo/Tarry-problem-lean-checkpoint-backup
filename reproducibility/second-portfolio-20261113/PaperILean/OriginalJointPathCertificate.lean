import PaperILean.OriginalJointPathVariation

/-! The already proved original joint-path requirements, bundled without
changing their domains, witnesses, endpoint constants or variation bounds. -/
noncomputable section
namespace PaperI
open Set

def OriginalJointLargePathCertificate {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (s d K M : ℕ) : Prop :=
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
      (originalJointComponentScale D i p.val)

/-- Enlarging budgets retains the same endpoints and the same joint map. -/
theorem OriginalJointLargePathCertificate.mono {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    {D : JointComponentPartition (planarBoundedBandFamily G)} {i : Fin D.count}
    {s d K M s' d' K' M' : ℕ}
    (h : OriginalJointLargePathCertificate D i s d K M)
    (hs : s ≤ s') (hd : d ≤ d') (hK : K ≤ K') (hM : M ≤ M') :
    OriginalJointLargePathCertificate D i s' d' K' M' := by
  obtain ⟨a,b,g,ha,hb,hg,hgraph,hend,hpaths,hvar⟩ := h
  refine ⟨a,b,g,ha,hb,hg,hgraph,hend,?_,?_⟩
  · intro p
    obtain ⟨γ,hγ,A,hcard,hdeg,hA⟩ := hpaths p
    exact ⟨γ,hγ,A,hcard.trans hs,fun q hq => (hdeg q hq).trans hd,hA⟩
  · intro p
    exact (hvar p).mono hK hM (originalJointComponentScale_nonneg D i p.val)

theorem published_originalJointLargePathCertificates
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) :
    ∃ s d K M : ℕ, ∀ i : Fin D.count,
      OriginalJointLargePathCertificate D i s d K M :=
  published_originalJointLargePaths_uniform_catalogue hCAD hCell hHardt hQE hNash hPiece D

end PaperI
