import PaperILean.CylindricalJointConnectedPaths

/-! Both endpoints are real parameters before the joint graph is constructed
and before its format budget is extracted. This gives uniformity over all
parameters and endpoints of one fixed joint family. Ambient n,s,D uniformity
over varying input families is a subsequent obligation. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def endpointLiftRelation {ρ κ : Type} (S : Set ((ρ ⊕ κ) → ℝ)) :
    Set (((((ρ ⊕ κ) ⊕ κ) ⊕ κ)) → ℝ) :=
  {v | Sum.elim (fun r => v (Sum.inl (Sum.inl (Sum.inl r)))) (v ∘ Sum.inr) ∈ S}

theorem endpointLiftRelation_definable {ρ κ : Type} {S : Set ((ρ ⊕ κ) → ℝ)}
    (hS : (univ : Set ℝ).Definable Language.ring S) :
    (univ : Set ℝ).Definable Language.ring (endpointLiftRelation S) := by
  convert hS.preimage_comp
    (Sum.elim (fun r => Sum.inl (Sum.inl (Sum.inl r))) Sum.inr) using 1
  ext v
  have he : Sum.elim (fun r => v (Sum.inl (Sum.inl (Sum.inl r)))) (v ∘ Sum.inr) =
      v ∘ Sum.elim (fun r => Sum.inl (Sum.inl (Sum.inl r))) Sum.inr := by
    funext k; cases k <;> rfl
  change (_ ∈ S) ↔ (_ ∈ S)
  rw [he]

theorem endpointLiftRelation_fiber {ρ κ : Type} (S : Set ((ρ ⊕ κ) → ℝ))
    (q : ((ρ ⊕ κ) ⊕ κ) → ℝ) :
    projectionFiber (endpointLiftRelation S) q =
      projectionFiber S (fun r => q (Sum.inl (Sum.inl r))) := rfl

theorem published_cylindrical_endpoint_jointPath
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ) (P : Set (ρ → ℝ)) (S : Set ((ρ ⊕ Fin n) → ℝ))
    (hP : HasPolynomialSignDescription P) (hS : HasPolynomialSignDescription S)
    (hconn : ∀ p ∈ P, IsPreconnected (projectionFiber S p)) :
    Nonempty (JointSemialgebraicPath (cellChainEndpointDomain P S) (endpointLiftRelation S)
      (fun q k => q (Sum.inl (Sum.inr k))) (fun q k => q (Sum.inr k))) := by
  have hD := cellChainEndpointDomain_definable
    (hasPolynomialSignDescription_definable hP) (hasPolynomialSignDescription_definable hS)
  apply published_cylindrical_jointPath_sections hCAD hQE n _ _ _ _
    (hQE.finite_sign_description _ hD)
    (hQE.finite_sign_description _ (endpointLiftRelation_definable
      (hasPolynomialSignDescription_definable hS)))
    (hQE.finite_sign_description _ (coordinateSectionGraph_definable hD
      (fun k => Sum.inl (Sum.inr k))))
    (hQE.finite_sign_description _ (coordinateSectionGraph_definable hD Sum.inr))
  · intro q hq
    exact hconn _ hq.1
  · intro q hq
    exact hq.2.1
  · intro q hq
    exact hq.2.2

/-- A single semialgebraic graph and budget precede all original parameters
and both arbitrary endpoints. The exact fiber, endpoint order and n=0 remain. -/
theorem published_cylindrical_connected_family_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ) (P : Set (ρ → ℝ)) (S : Set ((ρ ⊕ Fin n) → ℝ))
    (hP : HasPolynomialSignDescription P) (hS : HasPolynomialSignDescription S)
    (hconn : ∀ p ∈ P, IsPreconnected (projectionFiber S p)) :
    ∃ (g : (((ρ ⊕ Fin n) ⊕ Fin n) → ℝ) → ℝ → Fin n → ℝ) (s d : ℕ),
      HasPolynomialSignDescription (jointUnitPathGraph (cellChainEndpointDomain P S) g) ∧
      ∀ p ∈ P, ∀ a ∈ projectionFiber S p, ∀ b ∈ projectionFiber S p,
        ∃ γ : SemialgebraicUnitPath (projectionFiber S p) a b,
          γ.toFun = g (Sum.elim (Sum.elim p a) b) ∧
          ∃ A : Finset (MvPolynomial (Unit ⊕ Fin n) ℝ), A.card ≤ s ∧
            (∀ q ∈ A, q.totalDegree ≤ d) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨g⟩ := published_cylindrical_endpoint_jointPath hCAD hQE n P S hP hS hconn
  obtain ⟨s,d,hfmt⟩ := g.uniform_format
  refine ⟨g.toFun,s,d,g.graph,?_⟩
  intro p hp a ha b hb
  exact hfmt (Sum.elim (Sum.elim p a) b) ⟨hp,ha,hb⟩

end PaperI
