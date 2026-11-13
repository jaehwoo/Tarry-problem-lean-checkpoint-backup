import PaperILean.CylindricalJointPathData

/-! One complete oriented chain on its active region. Representatives are
chosen jointly inside actual cells. Each edge uses these same representatives,
so all joins are exact. The zero-edge case still connects distinct endpoints. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable

theorem cellChainEligibility_vertex_nonempty {ρ κ ι : Type*} [Fintype ι]
    {C : ι → Set ((ρ ⊕ κ) → ℝ)} {c : BoundedCellChain ι}
    {q : ((ρ ⊕ κ) ⊕ κ) → ℝ} (hq : q ∈ cellChainEligibility C c)
    (v : Fin (c.1.val+1)) :
    (projectionFiber (C (c.2 v)) (fun r => q (Sum.inl (Sum.inl r)))).Nonempty := by
  refine Fin.cases ?_ (fun i => ?_) v
  · exact ⟨(fun k => q (Sum.inl (Sum.inr k))),hq.1⟩
  · exact (closureAttachmentGraph_adj_nonempty (hq.2.2.2 i)).2

theorem published_cylindrical_oriented_chain_jointPath
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] {n : ℕ} {T : Set (ρ → ℝ)} {E : Set (CADVariables ρ n → ℝ)}
    (d : CylindricalInitialBandDecomposition n T (cadTimeCylinder n E))
    (c : OrientedBoundedCellChain d.slicedLeaf) (P : Set (ρ → ℝ))
    (x y : (ρ → ℝ) → Fin n → ℝ)
    (hP : HasPolynomialSignDescription P)
    (hX : HasPolynomialSignDescription (selectedFunctionGraph P x))
    (hY : HasPolynomialSignDescription (selectedFunctionGraph P y))
    (helig : ∀ p ∈ P, Sum.elim (Sum.elim p (x p)) (y p) ∈
      orientedCellChainEligibility d.slicedFiberCell c) :
    Nonempty (JointSemialgebraicPath P (cadPackedRelation n E) x y) := by
  classical
  have hrep : ∀ v : Fin (c.1.1.val+1), ∃ r : (ρ → ℝ) → Fin n → ℝ,
      HasPolynomialSignDescription (selectedFunctionGraph P r) ∧
      ∀ p ∈ P, r p ∈ projectionFiber (d.slicedFiberCell (c.1.2 v)) p := by
    intro v
    apply published_cylindrical_selector_fin hCAD hQE n P
      (d.slicedFiberCell (c.1.2 v)) hP
      (hQE.finite_sign_description _ (d.slicedFiberCell_definable (c.1.2 v)))
    intro p hp
    exact cellChainEligibility_vertex_nonempty (helig p hp).1 v
  choose r hR hr using hrep
  have hedge : ∀ i : Fin c.1.1.val,
      Nonempty (JointSemialgebraicPath P (cadPackedRelation n E) (r i.castSucc) (r i.succ)) := by
    intro i
    by_cases hi : c.2 i = true
    · apply published_cylindrical_directed_jointPath hCAD hQE d
        (c.1.2 i.castSucc) (c.1.2 i.succ) (r i.castSucc) (r i.succ)
        (fun p hp => ?_) (hR _) (hR _) (hr _) (hr _)
      simpa only [orientedCellChainSource,orientedCellChainTarget,hi,↓reduceIte]
        using (helig p hp).2 i
    · obtain ⟨g⟩ := published_cylindrical_directed_jointPath hCAD hQE d
        (c.1.2 i.succ) (c.1.2 i.castSucc) (r i.succ) (r i.castSucc)
        (fun p hp => by
          simpa only [orientedCellChainSource,orientedCellChainTarget,hi,↓reduceIte]
            using (helig p hp).2 i) (hR _) (hR _) (hr _) (hr _)
      exact ⟨g.reverse⟩
  obtain ⟨start⟩ := published_cylindrical_slice_jointPath hQE d (c.1.2 0) x (r 0)
    hX (hR _) (fun p hp => (helig p hp).1.1) (hr _)
  obtain ⟨finish⟩ := published_cylindrical_slice_jointPath hQE d
    (c.1.2 (Fin.last c.1.1.val)) (r (Fin.last c.1.1.val)) y
    (hR _) hY (hr _) (fun p hp => (helig p hp).1.2.1)
  exact ⟨(JointSemialgebraicPath.chain c.1.1.val r start (fun i => Classical.choice (hedge i))).trans finish⟩

end PaperI
