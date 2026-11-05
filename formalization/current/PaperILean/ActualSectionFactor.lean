import PaperILean.FixedDRelativeStage
import PaperILean.FixedDFiberComponents
import PaperILean.ActualDSections

/-! I3228[199,332): the actual right factor for an eligible component section.
The fixed-d relative estimate is applied to the literal fiber of E at g 3.
The section and the state are in that same component by actualDRegion;
no relative estimate or new assignment premise is supplied. -/
noncomputable section
namespace PaperI.ActualSectionFactor
open Set ActualDSections FixedDFiberComponents FixedDRelativeStage
  RegularSectionDifferential RegularSectionRates

private theorem section_times_relative (v g : Fin 6 → ℝ) :
    originalUpperAffineComp v (originalUpperRelativeFrame v g) = g := by
  rw [originalUpperRelativeFrame, ← originalUpperAffineComp_assoc,
    (originalUpperAffineComp_inv v).2]
  funext i
  fin_cases i <;> simp [originalUpperAffineComp]

/-- Uniform actual component-section attachment, with the original homogeneous
matrix and its actual inverse. The exponent is chosen before all chart data
and before the atlas, section label, or assigned state. -/
theorem actual_component_section_factor
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) (hk : 2 ≤ k) :
    ∃ M : ℕ, ∀ (P Cs Cw : ℝ) (S0 : AugmentedState k)
      (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ)),
      2 ≤ P → A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) →
      PolynomialSignDetermined A E →
      (∀ g ∈ E, augmentedStateNorm (augmentedPullback S0 g) ≤ P^Cw) →
      (∀ g ∈ E, P^(-Cs) ≤ descendingSingularValues
        (dComplement (augmentedPullback S0 g)) (Fin.last 4)) →
      ∀ (F : ComponentSectionAtlas (actualDRelation E)) (q : SectionLabel F)
        (g : Fin 6 → ℝ), g ∈ actualDRegion F q →
      ∃ hp : (fun _ : Fin 1 => g 3) ∈ F.piece q.1,
        let v := F.sectionFn q.1 q.2 ⟨_, hp⟩
        v ∈ E ∧ v 3 = g 3 ∧
        ∃ u : Fin 6 → ℝ,
          u = originalUpperRelativeFrame v g ∧
          g = originalUpperAffineComp v u ∧ u 3 = 0 ∧
          matrixFullHSNorm (originalAffineHomogeneousMatrix u) +
            matrixFullHSNorm ((originalAffineHomogeneousMatrix u)⁻¹) ≤
            P^((M : ℝ)*(6*(Fintype.card (AugmentedCoordinateIndex k) : ℝ)+
              3*max Cs 0+3*max Cw 0+4)+5) := by
  obtain ⟨M,hM⟩ := actual_fixed_d_relative_stage
    hCell hPath hHardt hQE hNash hPiece k (s+1) (max D 1) hk
  refine ⟨M,?_⟩
  intro P Cs Cw S0 A E hP hAc hAd hAE hwindow hσ F q g hg
  change ∃ hp : (fun _ : Fin 1 => g 3) ∈ F.piece q.1,
    g ∈ connectedComponentIn
      (projectionFiber (actualDRelation E) (fun _ : Fin 1 => g 3))
      (F.sectionFn q.1 q.2 ⟨_,hp⟩) at hg
  obtain ⟨hp,hg⟩ := hg
  let v := F.sectionFn q.1 q.2 ⟨fun _ : Fin 1 => g 3,hp⟩
  have hv : v ∈ {x : Fin 6 → ℝ | x ∈ E ∧ x 3 = g 3} :=
    F.section_mem q.1 q.2 ⟨_,hp⟩
  have hgv : g ∈ connectedComponentIn {x : Fin 6 → ℝ | x ∈ E ∧ x 3 = g 3} v := hg
  obtain ⟨B,hBc,hBd,hBE⟩ := actual_d_fiber_sign_format A E s D hAc hAd hAE (g 3)
  have hrel := hM P Cs Cw S0 B {x : Fin 6 → ℝ | x ∈ E ∧ x 3 = g 3}
    (g 3) hP hBc hBd hBE (fun x hx => hx.2)
    (fun x hx => hwindow x hx.1) (fun x hx => hσ x hx.1)
    v v g (mem_connectedComponentIn hv) hgv
  dsimp only at hrel
  refine ⟨hp,hv.1,hv.2,originalUpperRelativeFrame v g,rfl,
    (section_times_relative v g).symm,hrel.1,?_⟩
  simpa only [originalAffineHomogeneousMatrix_relative] using hrel.2

end PaperI.ActualSectionFactor
