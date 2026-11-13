import PaperILean.JointUnitPathMeasurability
import PaperILean.OriginalJointEndpointSelection

/-! I1263/I1265: specialize the original endpoint-parametric CAD path to
the common selected pair in the actual bounded-search component catalogue.
Format is uniform over all parameters/endpoints of this fixed catalogue.
Ambient input-format-only uniformity is not inferred from this statement. -/
noncomputable section
namespace PaperI
open Set

theorem JointComponentPartition.part_isPreconnected {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : JointComponentPartition A)
    (p : ρ → ℝ) (i : Fin D.count) :
    IsPreconnected (projectionFiber (D.part i) p) := by
  rcases (projectionFiber (D.part i) p).eq_empty_or_nonempty with he | ⟨x,hx⟩
  · rw [he]
    exact isPreconnected_empty
  · rw [D.component p i x hx]
    exact isPreconnected_connectedComponentIn

/-- The budget precedes all Borel endpoint choices. The SAME actual function
is jointly Borel and has the displayed semialgebraic time-section format. -/
theorem published_originalJointLargePaths_for_endpoints
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count) :
    ∃ s d : ℕ, ∀ a b : originalJointLargeComponentDomain D i → Fin 2 → ℝ,
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
  obtain ⟨g,s,d,hg,hpaths⟩ := published_cylindrical_connected_family_paths hCAD hQE 2
    univ (D.part i) ⟨∅,polynomialSignDetermined_univ⟩ (D.semialgebraic i)
    (fun p _ => D.part_isPreconnected p i)
  refine ⟨s,d,?_⟩
  intro a b ha hb haS hbS
  let p0 : originalJointLargeComponentDomain D i →
      (univ : Set (((ρ ⊕ Unit) ⊕ Unit) → ℝ)) := fun p => ⟨p.val,mem_univ _⟩
  have hp0 : Measurable p0 := measurable_subtype_coe.subtype_mk
  refine ⟨fun p => g (Sum.elim (Sum.elim p.val (a p)) (b p)),
    published_jointEndpointPath_measurable_comp hQE hHardt hg p0 a b hp0 ha hb haS hbS,?_⟩
  intro p
  exact hpaths p.val (mem_univ _) (a p) (haS p) (b p) (hbS p)

/-- A common path per valuation/catalogue entry, no label argument, and
exactly the endpoint constants of148. -/
theorem published_originalJointLargePaths
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count) :
    ∃ (s d : ℕ) (a b : originalJointLargeComponentDomain D i → Fin 2 → ℝ)
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
      ∀ p, ∃ γ : SemialgebraicUnitPath (projectionFiber (D.part i) p.val) (a p) (b p),
        γ.toFun = g p ∧ ∃ A : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ),
          A.card ≤ s ∧ (∀ q ∈ A, q.totalDegree ≤ d) ∧
          PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨s,d,hpaths⟩ := published_originalJointLargePaths_for_endpoints hCAD hQE hHardt D i
  obtain ⟨a,b,ha,hb,_,hend⟩ := published_originalJointLargeEndpoints hCAD hQE hHardt D i
  obtain ⟨g,hg,hpath⟩ := hpaths a b ha hb (fun p => (hend p).1) (fun p => (hend p).2.1)
  exact ⟨s,d,a,b,g,ha,hb,hg,jointRestrictedPath_graph_measurable g hg,hend,hpath⟩

theorem originalJointPath_mem_actual_component {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (p : ρ → ℝ) {T W : ℝ} (hT : 0 ≤ T) (hW : 0 < W)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G p)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    (i : Fin D.count) (z : WithLp 2 (Fin 2 → ℝ))
    (hz : (WithLp.equiv 2 (Fin 2 → ℝ)) z ∈ projectionFiber (D.part i)
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)))
    {a b : Fin 2 → ℝ}
    (γ : SemialgebraicUnitPath (projectionFiber (D.part i)
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W))) a b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ.toFun t) ∈ bufferedBandComponent E W z :=
  originalJointEndpoint_mem_actual_component D p hT hW ho hE hbox i z hz (γ.mapsTo ht)

theorem originalDyadicComponentAssigned_path_mem {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) {ω : Ω} {j : Λ} {k : ℤ} {i : Fin D.count}
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E) (hT : 0 ≤ radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω))
    (z : WithLp 2 (Fin 2 → ℝ))
    (hpoint : point ω j = (WithLp.equiv 2 (Fin 2 → ℝ)) z)
    (hj : originalDyadicComponentAssigned D active param radius point ω j k i)
    {a b : Fin 2 → ℝ}
    (γ : SemialgebraicUnitPath (projectionFiber (D.part i)
      (Sum.elim (Sum.elim (param ω) (fun _ => radius ω)) (fun _ => (2:ℝ)^k))) a b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ.toFun t) ∈
      bufferedBandComponent E ((2:ℝ)^k) z :=
  originalDyadicComponentAssigned_endpoint_mem D active param radius point ho hT hE hbox
    z hpoint hj (γ.mapsTo ht)

end PaperI
