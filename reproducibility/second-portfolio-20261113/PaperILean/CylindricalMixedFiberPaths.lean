import PaperILean.CylindricalAdmissiblePaths

/-! A joint graph on an explicitly definable admissible endpoint domain for
an arbitrary fixed family. Every pair in every preconnected fiber belongs to
this domain; other fibers need not be preconnected. Budgets precede p,a,b. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem published_cylindrical_mixed_family_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ) (S : Set ((ρ ⊕ Fin n) → ℝ))
    (hS : HasPolynomialSignDescription S) :
    ∃ (R : Set (((ρ ⊕ Fin n) ⊕ Fin n) → ℝ))
      (g : (((ρ ⊕ Fin n) ⊕ Fin n) → ℝ) → ℝ → Fin n → ℝ) (s d : ℕ),
      R ⊆ cellChainEndpointDomain univ S ∧ HasPolynomialSignDescription R ∧
      HasPolynomialSignDescription (jointUnitPathGraph R g) ∧
      (∀ q ∈ R, ∃ γ : SemialgebraicUnitPath
        (projectionFiber S (fun r => q (Sum.inl (Sum.inl r))))
        (fun k => q (Sum.inl (Sum.inr k))) (fun k => q (Sum.inr k)),
        γ.toFun = g q) ∧
      ∀ p, IsPreconnected (projectionFiber S p) →
        ∀ a ∈ projectionFiber S p, ∀ b ∈ projectionFiber S p,
          Sum.elim (Sum.elim p a) b ∈ R ∧
          ∃ γ : SemialgebraicUnitPath (projectionFiber S p) a b,
            γ.toFun = g (Sum.elim (Sum.elim p a) b) ∧
            ∃ A : Finset (MvPolynomial (Unit ⊕ Fin n) ℝ), A.card ≤ s ∧
              (∀ v ∈ A, v.totalDegree ≤ d) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  classical
  let D := cellChainEndpointDomain (univ : Set (ρ → ℝ)) S
  let T := endpointLiftRelation S
  let x := fun (q : ((ρ ⊕ Fin n) ⊕ Fin n) → ℝ) k => q (Sum.inl (Sum.inr k))
  let y := fun (q : ((ρ ⊕ Fin n) ⊕ Fin n) → ℝ) k => q (Sum.inr k)
  have hD := cellChainEndpointDomain_definable Set.definable_univ
    (hasPolynomialSignDescription_definable hS)
  have hT := endpointLiftRelation_definable (hasPolynomialSignDescription_definable hS)
  have hE := hQE.finite_sign_description _ (cadUnpackedRelation_definable n hT)
  obtain ⟨d⟩ := published_cylindrical_timeCylinder_decomposition hCAD hQE n D
    (cadUnpackedRelation n T) (hQE.finite_sign_description D hD) hE
  have hX := coordinateSectionGraph_definable hD (fun k => Sum.inl (Sum.inr k))
  have hY := coordinateSectionGraph_definable hD (Sum.inr : Fin n → (ρ ⊕ Fin n) ⊕ Fin n)
  let R := orientedChainSectionDomain D d.slicedFiberCell x y
  have hR := hQE.finite_sign_description R (orientedChainSectionDomain_definable
    D d.slicedFiberCell x y hD d.slicedFiberCell_definable hX hY)
  have he := cadPackedRelation_unpacked n T
  have hg := published_cylindrical_admissible_jointPath hCAD hQE d D x y
    (hQE.finite_sign_description D hD) (hQE.finite_sign_description _ hX)
    (hQE.finite_sign_description _ hY)
  have hg' : Nonempty (JointSemialgebraicPath R T x y) := by simpa only [he] using hg
  obtain ⟨g⟩ := hg'
  obtain ⟨sp,dp,hfmt⟩ := g.uniform_format
  refine ⟨R,g.toFun,sp,dp,orientedChainSectionDomain_subset D d.slicedFiberCell x y,
    hR,g.graph,g.path,?_⟩
  intro p hp a ha b hb
  let q := Sum.elim (Sum.elim p a) b
  have hq : q ∈ D := ⟨mem_univ p,ha,hb⟩
  have hc : IsPreconnected (projectionFiber (cadPackedRelation n (cadUnpackedRelation n T)) q) := by
    rw [he]
    exact hp
  have hx : x q ∈ projectionFiber (cadPackedRelation n (cadUnpackedRelation n T)) q := by
    rw [he]
    exact ha
  have hy : y q ∈ projectionFiber (cadPackedRelation n (cadUnpackedRelation n T)) q := by
    rw [he]
    exact hb
  have hqR : q ∈ R := mem_orientedChainSectionDomain_of_preconnected
    D d.slicedFiberCell x y hq _ hc (fun j => d.slicedFiberCell_subset j q)
    (fun _ hz => d.slicedFiberCell_cover hq hz) hx hy
  exact ⟨hqR,hfmt q hqR⟩

theorem published_cylindrical_family_uniform_endpoint_path_format
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ) (S : Set ((ρ ⊕ Fin n) → ℝ))
    (hS : HasPolynomialSignDescription S) :
    ∃ sPath dPath : ℕ, ∀ p, IsPreconnected (projectionFiber S p) →
      ∀ a ∈ projectionFiber S p, ∀ b ∈ projectionFiber S p,
        ∃ γ : SemialgebraicUnitPath (projectionFiber S p) a b,
          ∃ A : Finset (MvPolynomial (Unit ⊕ Fin n) ℝ), A.card ≤ sPath ∧
            (∀ v ∈ A, v.totalDegree ≤ dPath) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨R,g,sp,dp,_,_,_,_,h⟩ := published_cylindrical_mixed_family_paths hCAD hQE n S hS
  refine ⟨sp,dp,?_⟩
  intro p hp a ha b hb
  obtain ⟨_,γ,_,hγ⟩ := h p hp a ha b hb
  exact ⟨γ,hγ⟩

end PaperI
