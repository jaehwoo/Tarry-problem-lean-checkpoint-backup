import PaperILean.CylindricalFiniteGraphCover
import PaperILean.OriginalGaussJointPolynomial
import PaperILean.JointBivariateRegularRelation

/-! I1283/I1317/I1323, original CAD route: one common finite continuous
semialgebraic catalogue for the actual regular Gauss roots, jointly in all
phase coefficients and (p,z), chosen before labels and anchors. The planar-cell
refinement, cut continuations and quantitative conditioned estimates remain
separate obligations. No new external input is introduced. -/

noncomputable section
namespace PaperI
open Set FirstOrder Filter
open scoped Topology
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem originalGaussJointFirst_specialize {k : ℕ} (F : CoefficientSpace k)
    (n : ℕ) (p z : ℝ) :
    jointBivariateSpecialize (originalGaussJointFirstPolynomial k n) (Sum.elim F ![p,z]) =
      originalGaussPolynomialSlice (originalNormalPolynomial F n) z := by
  apply MvPolynomial.funext
  intro w
  rw [jointBivariateSpecialize_eval,originalGaussJointFirstPolynomial_eval,
    originalGaussPolynomialSlice_eval,originalNormalPhase_eq_eval]

theorem originalGaussJointSecond_specialize {k : ℕ} (F : CoefficientSpace k)
    (n : ℕ) (p z : ℝ) :
    jointBivariateSpecialize (originalGaussJointSecondPolynomial k n) (Sum.elim F ![p,z]) =
      originalGaussPolynomialSlice (originalGaussSecondPolynomial F n p) z := by
  apply MvPolynomial.funext
  intro w
  rw [jointBivariateSpecialize_eval,originalGaussJointSecondPolynomial_eval,
    originalGaussPolynomialSlice_eval]

theorem originalGaussJointJacobian_eval {k : ℕ} (F : CoefficientSpace k)
    (n : ℕ) (p z : ℝ) (w : Fin 2 → ℝ) :
    MvPolynomial.eval (Sum.elim (Sum.elim F ![p,z]) w)
      (jointBivariateJacobianPolynomial (originalGaussJointFirstPolynomial k n)
        (originalGaussJointSecondPolynomial k n)) =
      (originalGaussRootJacobian (originalGaussPhaseSlice (originalNormalPhase F n) z) p w).det := by
  rw [jointBivariateJacobianPolynomial_eval,originalGaussJointFirst_specialize,
    originalGaussJointSecond_specialize,originalGauss_polynomial_jacobian]

def originalGaussJointRegularRelation (k n : ℕ) :
    Set ((OriginalGaussParameters k ⊕ Fin 2) → ℝ) :=
  jointBivariateRegularRelation (originalGaussJointFirstPolynomial k n)
    (originalGaussJointSecondPolynomial k n)

theorem originalGaussJointRegularRelation_fiber {k : ℕ} (F : CoefficientSpace k)
    (n : ℕ) (p z : ℝ) :
    projectionFiber (originalGaussJointRegularRelation k n) (Sum.elim F ![p,z]) =
      originalGaussRegularRootSet F n p z := by
  ext w
  change (MvPolynomial.eval _ (originalGaussJointFirstPolynomial k n)=0 ∧
    MvPolynomial.eval _ (originalGaussJointSecondPolynomial k n)=0 ∧
    MvPolynomial.eval _ (jointBivariateJacobianPolynomial _ _)≠0) ↔ _
  rw [originalGaussJointFirstPolynomial_eval,originalGaussJointSecondPolynomial_eval,
    originalGaussSecondPolynomial_eval,originalGaussJointJacobian_eval]
  rfl

theorem originalGaussJointRegularRelation_definable (k n : ℕ) :
    (univ : Set ℝ).Definable Language.ring (originalGaussJointRegularRelation k n) :=
  jointBivariateRegularRelation_definable _ _

theorem published_originalGauss_joint_fibers_finite
    (cited : PublishedBivariateNonsingularBezout) (k m : ℕ) (hm : 2≤m) (hmk : m≤k/2)
    (a : OriginalGaussParameters k → ℝ) :
    (projectionFiber (originalGaussJointRegularRelation k (m-1)) a).Finite := by
  let F : CoefficientSpace k := a ∘ Sum.inl
  have ha : Sum.elim F ![a (Sum.inr 0),a (Sum.inr 1)] = a := by
    funext i
    cases i with
    | inl j => rfl
    | inr j => fin_cases j <;> rfl
  rw [← ha,originalGaussJointRegularRelation_fiber]
  obtain ⟨s,hs,_⟩ := published_originalGauss_regular_root_count cited F m hm hmk
    (a (Sum.inr 0)) (a (Sum.inr 1))
  have he : originalGaussRegularRootSet F (m-1) (a (Sum.inr 0)) (a (Sum.inr 1)) = (s : Set _) :=
    Set.ext (fun w => (hs w).symm)
  rw [he]
  exact s.finite_toSet

theorem published_originalGauss_common_root_cover
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    (cited : PublishedBivariateNonsingularBezout) (k m : ℕ) (hm : 2≤m) (hmk : m≤k/2) :
    Nonempty (CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k (m-1))) :=
  published_cylindrical_finite_graph_cover hCAD hQE 2 univ _
    (hQE.finite_sign_description _ Set.definable_univ)
    (hQE.finite_sign_description _ (originalGaussJointRegularRelation_definable k (m-1)))
    (fun a _ => published_originalGauss_joint_fibers_finite cited k m hm hmk a)

theorem originalGauss_common_root_cover_exact {k n : ℕ}
    (C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k n))
    (F : CoefficientSpace k) (p z : ℝ) (w : Fin 2 → ℝ) :
    w ∈ originalGaussRegularRootSet F n p z ↔
      ∃ i, Sum.elim F ![p,z] ∈ C.domain i ∧ w=C.sectionMap i (Sum.elim F ![p,z]) := by
  rw [← originalGaussJointRegularRelation_fiber]
  exact C.cover _ (mem_univ _) w

theorem originalGauss_common_root_cover_retains_graph {k : ℕ} (m : ℕ)
    (C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k (m-1)))
    (hm : 2≤m) (F : CoefficientSpace k) (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ)
    (hc : ContDiffAt ℝ 2 c ![y,z])
    (hroot : ∀ᶠ v in 𝓝 (![y,z] : Fin 2 → ℝ), originalNormalPhase F (m-1) ![c v,v 0,v 1]=0)
    (hk : originalNormalPhase F m ![c ![y,z],y,z]≠0)
    (hr : fderiv ℝ (fun v => fderiv ℝ c v ![1,0]) ![y,z] ![1,0]≠0) :
    ∃ i, Sum.elim F ![fderiv ℝ c ![y,z] ![1,0],z] ∈ C.domain i ∧
      ![c ![y,z],y] = C.sectionMap i (Sum.elim F ![fderiv ℝ c ![y,z] ![1,0],z]) := by
  apply (originalGauss_common_root_cover_exact C F _ z _).mp
  apply originalNormal_graph_mem_regular_roots F (m-1) c y z hc hroot _ hr
  simpa only [show m-1+1=m by omega] using hk

/-- The catalogue size and graph sign formats depend on k alone, uniformly in
the entire manuscript range of m and in F,p,z. These are existence bounds;
they are not effective exponents, derivative bounds, or continuation radii. -/
theorem published_originalGauss_uniform_catalogue_format
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    (cited : PublishedBivariateNonsingularBezout) (k : ℕ) :
    ∃ N s d : ℕ, ∀ m : ℕ, 2≤m → m≤k/2 →
      ∃ C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k (m-1)),
        C.count≤N ∧ ∀ i, ∃ A : Finset (MvPolynomial (OriginalGaussParameters k ⊕ Fin 2) ℝ),
          A.card≤s ∧ (∀ q ∈ A, q.totalDegree≤d) ∧
          PolynomialSignDetermined A (selectedFunctionGraph (C.domain i) (C.sectionMap i)) := by
  classical
  let I := {m : Fin (k+1) // 2≤m.val ∧ m.val≤k/2}
  let C := fun i : I => Classical.choice
    (published_originalGauss_common_root_cover hCAD hQE cited k i.val.val i.property.1 i.property.2)
  have hfmt := fun i : I => (C i).common_graph_format
  choose s d hsd using hfmt
  refine ⟨Finset.univ.sup (fun i : I => (C i).count),Finset.univ.sup s,Finset.univ.sup d,?_⟩
  intro m hm hmk
  have hmk' : m≤k := hmk.trans (Nat.div_le_self k 2)
  let i : I := ⟨⟨m,by omega⟩,hm,hmk⟩
  refine ⟨C i,Finset.le_sup (f := fun j : I => (C j).count) (Finset.mem_univ i),?_⟩
  intro j
  obtain ⟨A,hA,hdeg,hS⟩ := hsd i j
  exact ⟨A,hA.trans (Finset.le_sup (f := s) (Finset.mem_univ i)),
    fun q hq => (hdeg q hq).trans (Finset.le_sup (f := d) (Finset.mem_univ i)),hS⟩

end PaperI
