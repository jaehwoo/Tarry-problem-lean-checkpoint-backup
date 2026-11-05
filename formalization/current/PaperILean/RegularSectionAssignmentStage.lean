import PaperILean.ActualSectionFactor
import PaperILean.ExceptionalDSections

/-! Complete assertion(i), I3228[22,496). The actual fixed-order assignment
is constructed together with its original section atlas and exceptional list.
The newly supplied implication is I3228[199,332): each assigned state is
an actual bounded right translate of its chosen section. Saved constituent
proof stages are reused without repeat completion credit. -/
noncomputable section
open scoped BigOperators
namespace PaperI.RegularSectionAssignmentStage
open Set Matrix ActualDSections ExceptionalDSections
open RegularSectionDifferential RegularSectionRates

/-- All constants precede the actual chart coefficients, orbit seed, scales and
assigned states. The entire existing axis/section certificate is retained. -/
theorem regular_d_sections_assertion_i
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) (hk : 2 ≤ k) :
    ∃ N sOut dOut K M : ℕ,
      ∀ (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A E →
      ∃ (F : ComponentSectionAtlas (actualDRelation E)) (C : Finset ℝ)
        (assignment : FixedOrderAssignment F sOut dOut),
        F.Bounded N sOut dOut ∧ Fintype.card (SectionLabel F) ≤ N*N ∧
        (∀ i j (p : F.piece i), F.sectionFn i j p ∈ E ∧
          (F.sectionFn i j p) 3 = p.val 0) ∧
        C.card ≤ K ∧ C.powerset.card ≤ 2^K ∧
        (∀ t : ℝ, t ∈ C ∨ ∃ L ∈ C.powerset, t ∈ axisCutCell C L) ∧
        (∀ L ∈ C.powerset, ∀ M ∈ C.powerset, L ≠ M →
          Disjoint (axisCutCell C L) (axisCutCell C M)) ∧
        (∀ L ∈ C.powerset, IsOpen (axisCutCell C L) ∧
          IsPreconnected (axisCutCell C L) ∧
          (∀ t ∈ axisCutCell C L, t ∉ C) ∧
          ((∀ t ∈ axisCutCell C L,
              projectionFiber (actualDRelation E) (fun _ => t) = ∅) ∨
            ∃ (i : Fin F.n) (hU : parameterCell C L ⊆ F.piece i),
              (∀ j : Fin (F.m i),
                Continuous (restrictSection F i j C L hU) ∧
                HasBoundedSignFormat (sOut+K) (max dOut 1)
                  (componentSectionGraph (parameterCell C L) (restrictSection F i j C L hU)) ∧
                HasBoundedSignFormat (sOut+K) (max dOut 1)
                  (componentSectionRegion (actualDRelation E) (parameterCell C L)
                    (restrictSection F i j C L hU))) ∧
              (∀ j (p : parameterCell C L),
                restrictSection F i j C L hU p ∈ E ∧
                (restrictSection F i j C L hU p) 3 = p.val 0) ∧
              ∀ p : parameterCell C L, Function.Bijective
                (fun j => ConnectedComponents.mk
                  (⟨restrictSection F i j C L hU p,
                    F.section_mem i j ⟨p.val,hU p.property⟩⟩ :
                    projectionFiber (actualDRelation E) p.val)))) ∧
        (∀ (P Cs Cw : ℝ) (S0 : AugmentedState k),
          2 ≤ P →
          (∀ g ∈ E, augmentedStateNorm (augmentedPullback S0 g) ≤ P^Cw) →
          (∀ g ∈ E, P^(-Cs) ≤ descendingSingularValues
            (dComplement (augmentedPullback S0 g)) (Fin.last 4)) →
          ∀ g : E, ∃ hp : (fun _ : Fin 1 => g.val 3) ∈ F.piece (assignment.pick g).1,
            let v := F.sectionFn (assignment.pick g).1 (assignment.pick g).2 ⟨_,hp⟩
            v ∈ E ∧ v 3 = g.val 3 ∧ ∃ u : Fin 6 → ℝ,
              u = originalUpperRelativeFrame v g.val ∧
              g.val = originalUpperAffineComp v u ∧ u 3 = 0 ∧
              matrixFullHSNorm (originalAffineHomogeneousMatrix u) +
                matrixFullHSNorm ((originalAffineHomogeneousMatrix u)⁻¹) ≤
                P^((M : ℝ)*(6*(Fintype.card (AugmentedCoordinateIndex k) : ℝ)+
                  3*max Cs 0+3*max Cw 0+4)+5)) := by
  classical
  obtain ⟨N,sOut,dOut,K,hAtlas⟩ := ExceptionalDSections.actual_d_exceptional_list
    hCell hHardt hQE s D
  obtain ⟨M,hFactor⟩ := ActualSectionFactor.actual_component_section_factor
    hCell hPath hHardt hQE hNash hPiece k s D hk
  refine ⟨N,sOut,dOut,K,M,?_⟩
  intro A E hAc hAd hAE
  obtain ⟨F,C,hF,⟨assignment⟩,hC,hPower,hCover,hDisjoint,hCells⟩ := hAtlas A E hAc hAd hAE
  have hCount : Fintype.card (SectionLabel F) ≤ N*N := by
    calc
      Fintype.card (SectionLabel F) = ∑ i : Fin F.n, F.m i := by
        simp [SectionLabel,Fintype.card_sigma]
      _ ≤ ∑ _i : Fin F.n, N := Finset.sum_le_sum (fun i _ => hF.sections_le i)
      _ = F.n*N := by simp
      _ ≤ N*N := Nat.mul_le_mul_right N hF.pieces_le
  refine ⟨F,C,assignment,hF,hCount,?_,hC,hPower,hCover,hDisjoint,hCells,?_⟩
  · intro i j p
    exact F.section_mem i j p
  · intro P Cs Cw S0 hP hWindow hPivot g
    have hg : g.val ∈ actualDRegion F (assignment.pick g) := by
      have h := assignment.pick_first g
      rw [assignment.first_region] at h
      exact h
    exact hFactor P Cs Cw S0 A E hP hAc hAd hAE hWindow hPivot
      F (assignment.pick g) g.val hg

end PaperI.RegularSectionAssignmentStage
