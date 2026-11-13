import PaperILean.CylindricalPathGraphs

/-! Uniformity over every pair of endpoints in every fiber of one supplied
cylindrical tower. Bounds precede the endpoints and their shared base parameter.
They may depend on the supplied tower; ambient-format uniformity and finite
whole-chain assembly are not asserted here. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def cadTowerEndpointPairs {α : Type} (n : ℕ) (S : Set (CADVariables α n → ℝ)) :
    Set ((CADVariables α n ⊕ CADVariables α n) → ℝ) :=
  {v | v ∘ Sum.inl ∈ S ∧ v ∘ Sum.inr ∈ S ∧
    (v ∘ Sum.inl) ∘ cadBaseCoordinate n = (v ∘ Sum.inr) ∘ cadBaseCoordinate n}

theorem cadTowerEndpointPairs_definable {α : Type} [Finite α] (n : ℕ)
    {S : Set (CADVariables α n → ℝ)}
    (hS : (univ : Set ℝ).Definable Language.ring S) :
    (univ : Set ℝ).Definable Language.ring (cadTowerEndpointPairs n S) := by
  letI : Fintype α := Fintype.ofFinite α
  have hE := realDefinable_finite_all (fun i : α => realPolynomial_zero_definable
    (MvPolynomial.X (Sum.inl (cadBaseCoordinate n i)) -
      MvPolynomial.X (Sum.inr (cadBaseCoordinate n i)) :
        MvPolynomial (CADVariables α n ⊕ CADVariables α n) ℝ))
  convert (hS.preimage_comp Sum.inl).inter ((hS.preimage_comp Sum.inr).inter hE) using 1
  ext v
  simp only [cadTowerEndpointPairs,mem_setOf_eq,mem_inter_iff,mem_preimage,
    map_sub,MvPolynomial.eval_X,sub_eq_zero,funext_iff,Function.comp_def]

theorem published_cylindricalTower_endpointPath_joint_semialgebraic
    (hQE : PublishedRealSemialgebraicity) {α : Type} [Finite α]
    {U : Set (α → ℝ)} {n : ℕ} {S : Set (CADVariables α n → ℝ)}
    (c : CylindricalTower U S)
    (hU : (univ : Set ℝ).Definable Language.ring U) :
    HasPolynomialSignDescription (jointUnitPathGraph (cadTowerEndpointPairs n S)
      (fun v => c.endpointPath (v ∘ Sum.inl) (v ∘ Sum.inr))) := by
  letI : Fintype (CADVariables α n) := Fintype.ofFinite _
  have hP := cadTowerEndpointPairs_definable n (c.region_definable hU)
  exact hQE.finite_sign_description _ (c.endpointPath_jointGraph_definable
    (coordinateSectionGraph_definable hP Sum.inl)
    (coordinateSectionGraph_definable hP Sum.inr)
    (fun _ hv => hv.1) (fun _ hv => hv.2.1))

theorem published_cylindricalTower_endpointPaths_bounded_format
    (hQE : PublishedRealSemialgebraicity) {α : Type} [Finite α]
    {U : Set (α → ℝ)} {n : ℕ} {S : Set (CADVariables α n → ℝ)}
    (c : CylindricalTower U S)
    (hU : (univ : Set ℝ).Definable Language.ring U) :
    ∃ sPath dPath : ℕ, ∀ a ∈ S, ∀ b ∈ S,
      a ∘ cadBaseCoordinate n = b ∘ cadBaseCoordinate n →
      ∃ γ : SemialgebraicUnitPath S a b,
        γ.toFun = c.endpointPath a b ∧
        (∀ t, γ.toFun t ∘ cadBaseCoordinate n = a ∘ cadBaseCoordinate n) ∧
        ∃ A : Finset (MvPolynomial (Unit ⊕ CADVariables α n) ℝ),
          A.card ≤ sPath ∧ (∀ q ∈ A, q.totalDegree ≤ dPath) ∧
          PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨sPath,dPath,hfmt⟩ := jointUnitPathGraph_uniform_fiber_format _ _
    (published_cylindricalTower_endpointPath_joint_semialgebraic hQE c hU)
  refine ⟨sPath,dPath,?_⟩
  intro a ha b hb hbase
  have hp : Sum.elim a b ∈ cadTowerEndpointPairs n S := ⟨ha,hb,hbase⟩
  obtain ⟨A,hs,hd,hA⟩ := hfmt (Sum.elim a b) hp
  have h := c.endpointPath_properties ha hb hbase
  exact ⟨⟨c.endpointPath a b,h.1,h.2.1,h.2.2.1,h.2.2.2.1,⟨A,hA⟩⟩,
    rfl,h.2.2.2.2,A,hs,hd,hA⟩

end PaperI
