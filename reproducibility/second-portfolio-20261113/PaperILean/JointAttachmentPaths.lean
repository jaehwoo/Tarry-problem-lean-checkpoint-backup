import PaperILean.JointChartSectionPaths
import PaperILean.JointHalfRadiusPaths
import PaperILean.JointCellAttachments

/-! Actual three-piece directed attachment paths, jointly in the parameter.
The chart families are explicit input data on the active domain; this module
does not obtain a joint atlas from the pointwise cell-decomposition contract.
The selected source is in the actual source cell and the other fiber's closure.
Pre-strategy evidence: checkpoint_116_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set

theorem selectedFunctionGraph_restrict {ρ κ : Type*}
    {P Q : Set (ρ → ℝ)} (hPQ : P ⊆ Q) (f : (ρ → ℝ) → κ → ℝ)
    (hP : HasPolynomialSignDescription P)
    (hG : HasPolynomialSignDescription (selectedFunctionGraph Q f)) :
    HasPolynomialSignDescription (selectedFunctionGraph P f) := by
  have h := (hasPolynomialSignDescription_polynomial_preimage hP
    (fun r => MvPolynomial.X (Sum.inl r : ρ ⊕ κ))).inter hG
  convert h using 1
  ext z
  simp only [selectedFunctionGraph,mem_setOf_eq,mem_inter_iff,MvPolynomial.eval_X]
  exact ⟨fun ⟨hp,hf⟩ => ⟨hp,hPQ hp,hf⟩, fun ⟨hp,_,hf⟩ => ⟨hp,hf⟩⟩

theorem published_joint_attachment_selector_on
    (hChoice : PublishedSemialgebraicDefinableChoice) (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (P : Set (ρ → ℝ)) (C D : Set ((ρ ⊕ κ) → ℝ))
    (hP : HasPolynomialSignDescription P) (hPD : P ⊆ directedCellAttachmentDomain C D)
    (hC : HasPolynomialSignDescription C) (hD : HasPolynomialSignDescription D) :
    ∃ a : (ρ → ℝ) → κ → ℝ,
      HasPolynomialSignDescription (selectedFunctionGraph P a) ∧
      ∀ p ∈ P, a p ∈ projectionFiber C p ∧ a p ∈ closure (projectionFiber D p) := by
  obtain ⟨a,hA,ha⟩ := published_joint_attachment_selector hChoice hQE C D hC hD
  exact ⟨a,selectedFunctionGraph_restrict hPD a hP hA,fun p hp => ha p (hPD hp)⟩

def jointChartGermPath {ρ κ : Type*} {dC dD : ℕ}
    (P : Set (ρ → ℝ)) (C D : Set ((ρ ⊕ κ) → ℝ))
    (eC : ∀ p : P, openUnitCube dC ≃ₜ projectionFiber C p.val)
    (eD : ∀ p : P, openUnitCube dD ≃ₜ projectionFiber D p.val)
    (x y a : (ρ → ℝ) → κ → ℝ)
    (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ)
    (hx : ∀ p ∈ P, x p ∈ projectionFiber C p)
    (hy : ∀ p ∈ P, y p ∈ projectionFiber D p)
    (ha : ∀ p ∈ P, a p ∈ projectionFiber C p)
    (hb : ∀ p ∈ P, g p (ε p/2) ∈ projectionFiber D p)
    (p : ρ → ℝ) : ℝ → κ → ℝ :=
  unitPathConcat (cellChartSectionPath P C eC x a hx ha p)
    (unitPathConcat (jointHalfRadiusPath ε g p)
      (cellChartSectionPath P D eD (fun p => g p (ε p/2)) y hb hy p))

theorem published_jointChartGermPath_semialgebraic
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Finite κ] {dC dD : ℕ}
    (P : Set (ρ → ℝ)) (C D : Set ((ρ ⊕ κ) → ℝ))
    (eC : ∀ p : P, openUnitCube dC ≃ₜ projectionFiber C p.val)
    (eD : ∀ p : P, openUnitCube dD ≃ₜ projectionFiber D p.val)
    (x y a : (ρ → ℝ) → κ → ℝ)
    (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ)
    (hx : ∀ p ∈ P, x p ∈ projectionFiber C p)
    (hy : ∀ p ∈ P, y p ∈ projectionFiber D p)
    (ha : ∀ p ∈ P, a p ∈ projectionFiber C p)
    (hb : ∀ p ∈ P, g p (ε p/2) ∈ projectionFiber D p)
    (hε : ∀ p ∈ P, 0 < ε p)
    (hEC : HasPolynomialSignDescription (jointCubeChartGraph P C eC))
    (hED : HasPolynomialSignDescription (jointCubeChartGraph P D eD))
    (hX : HasPolynomialSignDescription (selectedFunctionGraph P x))
    (hY : HasPolynomialSignDescription (selectedFunctionGraph P y))
    (hA : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hR : HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)))
    (hG : HasPolynomialSignDescription (jointCurveGermGraph P ε g)) :
    HasPolynomialSignDescription
      (jointUnitPathGraph P (jointChartGermPath P C D eC eD x y a ε g hx hy ha hb)) := by
  have hB := published_jointHalfRadiusEndpoint_semialgebraic hQE P ε g hε hR hG
  exact jointUnitPathGraph_concat_semialgebraic
    (published_cellChartSectionPath_joint_semialgebraic hQE P C eC x a hx ha hEC hX hA)
    (jointUnitPathGraph_concat_semialgebraic
      (published_jointHalfRadiusPath_semialgebraic hQE P ε g hε hR hG)
      (published_cellChartSectionPath_joint_semialgebraic hQE P D eD
        (fun p => g p (ε p/2)) y hb hy hED hB hY))

/-- The source, radius, germ and actual three-piece path are selected before
the parameter and containing ambient set. Budgets are for this supplied joint
family, not yet bounds depending only on the original ambient input format. -/
theorem published_joint_directed_attachment_paths
    (hChoice : PublishedSemialgebraicDefinableChoice)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {ρ κ : Type} [Finite ρ] [Fintype κ] {dC dD : ℕ}
    (P : Set (ρ → ℝ)) (C D : Set ((ρ ⊕ κ) → ℝ))
    (hPD : P ⊆ directedCellAttachmentDomain C D)
    (eC : ∀ p : P,
      openUnitCube dC ≃ₜ projectionFiber C p.val)
    (eD : ∀ p : P,
      openUnitCube dD ≃ₜ projectionFiber D p.val)
    (x y : (ρ → ℝ) → κ → ℝ)
    (hx : ∀ p ∈ P, x p ∈ projectionFiber C p)
    (hy : ∀ p ∈ P, y p ∈ projectionFiber D p)
    (hC : HasPolynomialSignDescription C) (hD : HasPolynomialSignDescription D)
    (hEC : HasPolynomialSignDescription (jointCubeChartGraph P C eC))
    (hED : HasPolynomialSignDescription (jointCubeChartGraph P D eD))
    (hX : HasPolynomialSignDescription (selectedFunctionGraph P x))
    (hY : HasPolynomialSignDescription (selectedFunctionGraph P y)) :
    ∃ (a : (ρ → ℝ) → κ → ℝ) (ε : (ρ → ℝ) → ℝ)
      (g : (ρ → ℝ) → ℝ → κ → ℝ)
      (ha : ∀ p ∈ P, a p ∈ projectionFiber C p)
      (hb : ∀ p ∈ P, g p (ε p/2) ∈ projectionFiber D p)
      (s d : ℕ),
      let η := jointChartGermPath P C D eC eD x y a ε g hx hy ha hb
      HasPolynomialSignDescription (selectedFunctionGraph P a) ∧
      HasPolynomialSignDescription
        (selectedFunctionGraph P (fun p (_ : Unit) => ε p)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph P ε g) ∧
      HasPolynomialSignDescription (jointUnitPathGraph P η) ∧
      (∀ p ∈ P,
        a p ∈ closure (projectionFiber D p) ∧ 0 < ε p ∧ ε p < 1 ∧ g p 0 = a p ∧
        ContinuousOn (g p) (Ico (0 : ℝ) (ε p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) (ε p)) (projectionFiber D p)) ∧
      ∀ p ∈ P, ∀ S : Set (κ → ℝ),
        projectionFiber C p ⊆ S → projectionFiber D p ⊆ S →
        ∃ γ : SemialgebraicUnitPath S (x p) (y p), γ.toFun = η p ∧
          ∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ), A.card ≤ s ∧
            (∀ q ∈ A, q.totalDegree ≤ d) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  have hP := hQE.finite_sign_description P (selectedFunctionGraph_domain_definable P x
    (hasPolynomialSignDescription_definable hX))
  obtain ⟨a,hA,hm⟩ := published_joint_attachment_selector_on hChoice hQE P C D hP hPD hC hD
  obtain ⟨ε,g,hR,hG,h⟩ := published_joint_curve_selection
    hChoice hQE hNash P D a hD hA (fun p hp => (hm p hp).2)
  have ha : ∀ p ∈ P, a p ∈ projectionFiber C p := fun p hp => (hm p hp).1
  have hε : ∀ p ∈ P, 0 < ε p := fun p hp => (h p hp).1
  have hb : ∀ p ∈ P, g p (ε p/2) ∈ projectionFiber D p := by
    intro p hp
    exact (h p hp).2.2.2.2 ⟨half_pos (hε p hp),by linarith [hε p hp]⟩
  let η := jointChartGermPath P C D eC eD x y a ε g hx hy ha hb
  have hη := published_jointChartGermPath_semialgebraic
    hQE P C D eC eD x y a ε g hx hy ha hb hε hEC hED hX hY hA hR hG
  obtain ⟨s,d,hfmt⟩ := jointUnitPathGraph_uniform_fiber_format P η hη
  have hB := published_jointHalfRadiusEndpoint_semialgebraic hQE P ε g hε hR hG
  obtain ⟨sL,dL,hL⟩ := published_cellChartSectionPath_bounded_unitPaths
    hQE P C eC x a hx ha hEC hX hA
  obtain ⟨sR,dR,hRight⟩ := published_cellChartSectionPath_bounded_unitPaths
    hQE P D eD (fun p => g p (ε p/2)) y hb hy hED hB hY
  obtain ⟨sG,dG,hgpaths⟩ := jointHalfRadiusPath_bounded_unitPaths P D ε g
    (published_jointHalfRadiusPath_semialgebraic hQE P ε g hε hR hG)
    (fun p hp => ⟨(h p hp).1,(h p hp).2.2.2⟩)
  refine ⟨a,ε,g,ha,hb,s,d,hA,hR,hG,hη,fun p hp => ⟨(hm p hp).2,h p hp⟩,?_⟩
  intro p hp S hCS hDS
  obtain ⟨γL,hγL,_⟩ := hL p hp
  obtain ⟨γR,hγR,_⟩ := hRight p hp
  obtain ⟨γG0,hγG,_,_⟩ := hgpaths p hp S
    (by rw [(h p hp).2.2.1]; exact hCS (ha p hp)) hDS
  let γG : SemialgebraicUnitPath S (a p) (g p (ε p/2)) :=
    { γG0 with source := γG0.source.trans (h p hp).2.2.1 }
  let γ := (γL.weaken hCS).trans (γG.trans (γR.weaken hDS))
  have he : γ.toFun = η p := by
    simp only [γ,η,jointChartGermPath,SemialgebraicUnitPath.trans_toFun,
      SemialgebraicUnitPath.weaken_toFun,γG,hγL,hγR,hγG]
  obtain ⟨A,hs,hd,hsign⟩ := hfmt p hp
  exact ⟨γ,he,A,hs,hd,by simpa only [he] using hsign⟩

end PaperI
