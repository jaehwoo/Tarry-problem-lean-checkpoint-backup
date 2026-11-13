import PaperILean.JointOriginalReadoutCuts
import PaperILean.OriginalUniformJointPaths

/-! Strengthen the ORIGINAL endpoint-parametric CAD path constructor BEFORE
forgetting its joint graph. Its actual time cuts and active count are now
Borel. Universal coefficients and finite maxima put all three budgets before
tables, coefficients, radii, widths, component entries and endpoint choices.
This is not a measurability assertion about arbitrary pointwise path encodings. -/
noncomputable section
namespace PaperI
open Set

theorem OriginalPlanarReadoutPartition.mono {g : ℝ → Fin 2 → ℝ} {K H n : ℕ} {t : ℕ → ℝ}
    (h : OriginalPlanarReadoutPartition g K n t) (hKH : K≤H) :
    OriginalPlanarReadoutPartition g H n t :=
  ⟨h.1,h.2.1.trans hKH,h.2.2⟩

def OriginalJointEndpointCutPathFamily {ρ : Type}
    (P : Set (ρ → ℝ)) (S : Set ((ρ ⊕ Fin 2) → ℝ)) (s d H : ℕ) : Prop :=
  ∃ (g : (((ρ ⊕ Fin 2) ⊕ Fin 2) → ℝ) → ℝ → Fin 2 → ℝ)
    (n : (((ρ ⊕ Fin 2) ⊕ Fin 2) → ℝ) → ℕ)
    (t : (((ρ ⊕ Fin 2) ⊕ Fin 2) → ℝ) → ℕ → ℝ),
    HasPolynomialSignDescription (jointUnitPathGraph (cellChainEndpointDomain P S) g) ∧
    Measurable n ∧ (∀ j, Measurable (fun q => t q j)) ∧
    (∀ p∈P, ∀ a∈projectionFiber S p, ∀ b∈projectionFiber S p,
      ∃ γ : SemialgebraicUnitPath (projectionFiber S p) a b,
        γ.toFun=g (Sum.elim (Sum.elim p a) b) ∧
        ∃ A : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ), A.card≤s ∧
          (∀ q∈A, q.totalDegree≤d) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun)) ∧
    ∀ q∈cellChainEndpointDomain P S, OriginalPlanarReadoutPartition (g q) H (n q) (t q)

theorem OriginalJointEndpointCutPathFamily.mono {ρ : Type}
    {P : Set (ρ → ℝ)} {S : Set ((ρ ⊕ Fin 2) → ℝ)} {s d H s' d' H' : ℕ}
    (h : OriginalJointEndpointCutPathFamily P S s d H)
    (hs : s≤s') (hd : d≤d') (hH : H≤H') :
    OriginalJointEndpointCutPathFamily P S s' d' H' := by
  obtain ⟨g,n,t,hg,hn,ht,hpath,hpart⟩ := h
  refine ⟨g,n,t,hg,hn,ht,?_,fun q hq => (hpart q hq).mono hH⟩
  intro p hp a ha b hb
  obtain ⟨γ,hγ,A,hcard,hdeg,hA⟩ := hpath p hp a ha b hb
  exact ⟨γ,hγ,A,hcard.trans hs,fun q hq => (hdeg q hq).trans hd,hA⟩

theorem published_cylindrical_connected_family_readout_cut_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    {ρ : Type} [Finite ρ] (P : Set (ρ → ℝ)) (S : Set ((ρ ⊕ Fin 2) → ℝ))
    (hP : HasPolynomialSignDescription P) (hS : HasPolynomialSignDescription S)
    (hconn : ∀ p∈P, IsPreconnected (projectionFiber S p)) :
    ∃ s d H : ℕ, OriginalJointEndpointCutPathFamily P S s d H := by
  obtain ⟨g,s,d,hg,hpath⟩ := published_cylindrical_connected_family_paths hCAD hQE 2 P S hP hS hconn
  obtain ⟨H,n,t,hn,ht,hpart⟩ := published_joint_original_planar_readout_partition
    hCAD hCell hHardt hQE hPiece (cellChainEndpointDomain P S) g hg
  exact ⟨s,d,H,g,n,t,hg,hn,ht,hpath,hpart⟩

/-- Both endpoint maps may be merely Borel. The selected cuts and path are
pullbacks of one common joint construction; equal endpoints are permitted. -/
theorem OriginalJointEndpointCutPathFamily.for_endpoints
    (hQE : PublishedRealSemialgebraicity) (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ : Type} [Finite ρ] {P : Set (ρ → ℝ)} {S : Set ((ρ ⊕ Fin 2) → ℝ)} {s d H : ℕ}
    (h : OriginalJointEndpointCutPathFamily P S s d H)
    {Ω : Type*} [MeasurableSpace Ω] (p : Ω → P) (a b : Ω → Fin 2 → ℝ)
    (hp : Measurable p) (ha : Measurable a) (hb : Measurable b)
    (haS : ∀ ω, a ω∈projectionFiber S (p ω).val)
    (hbS : ∀ ω, b ω∈projectionFiber S (p ω).val) :
    ∃ (g : Ω → ℝ → Fin 2 → ℝ) (n : Ω → ℕ) (t : Ω → ℕ → ℝ),
      Measurable (fun v : Ω × Icc (0:ℝ) 1 => g v.1 v.2.val) ∧
      Measurable n ∧ (∀ j, Measurable (fun ω => t ω j)) ∧
      (∀ ω, ∃ γ : SemialgebraicUnitPath (projectionFiber S (p ω).val) (a ω) (b ω),
        γ.toFun=g ω ∧ ∃ A : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ),
          A.card≤s ∧ (∀ q∈A, q.totalDegree≤d) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun)) ∧
      ∀ ω, OriginalPlanarReadoutPartition (g ω) H (n ω) (t ω) ∧
        ∀ j<n ω, OriginalPlanarGraphArc (g ω) (t ω j) (t ω (j+1)) := by
  obtain ⟨G,N,T,hG,hN,hT,hpath,hpart⟩ := h
  let q : Ω → cellChainEndpointDomain P S := fun ω =>
    ⟨Sum.elim (Sum.elim (p ω).val (a ω)) (b ω),(p ω).property,haS ω,hbS ω⟩
  have hq : Measurable q := by
    apply Measurable.subtype_mk
    apply measurable_pi_lambda
    intro i
    rcases i with (r | k) | k
    · exact (measurable_pi_apply r).comp (measurable_subtype_coe.comp hp)
    · exact (measurable_pi_apply k).comp ha
    · exact (measurable_pi_apply k).comp hb
  have hqv := measurable_subtype_coe.comp hq
  refine ⟨fun ω => G (q ω).val,fun ω => N (q ω).val,fun ω => T (q ω).val,
    published_jointUnitPath_measurable_comp hQE hHardt hG q hq,
    hN.comp hqv,fun j => (hT j).comp hqv,
    fun ω => hpath (p ω).val (p ω).property (a ω) (haS ω) (b ω) (hbS ω),?_⟩
  intro ω
  have hpartω := hpart (q ω).val (q ω).property
  refine ⟨hpartω,hpartω.graph_arcs ?_⟩
  obtain ⟨γ,hγ,_⟩ := hpath (p ω).val (p ω).property (a ω) (haS ω) (b ω) (hbS ω)
  change ContinuousOn (G (Sum.elim (Sum.elim (p ω).val (a ω)) (b ω))) (Icc (0:ℝ) 1)
  rw [← hγ]
  exact γ.continuousOn

theorem published_original_component_joint_readout_cut_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) :
    ∃ s d H : ℕ, 2≤H ∧ ∀ i : Fin D.count,
      OriginalJointEndpointCutPathFamily univ (D.part i) s d H := by
  classical
  have hi := fun i => published_cylindrical_connected_family_readout_cut_paths
    hCAD hCell hHardt hQE hPiece univ (D.part i) ⟨∅,polynomialSignDetermined_univ⟩
    (D.semialgebraic i) (fun p _ => D.part_isPreconnected p i)
  choose s d H h using hi
  refine ⟨Finset.univ.sup s,Finset.univ.sup d,Finset.univ.sup H+2,by omega,?_⟩
  intro i
  exact (h i).mono (Finset.le_sup (f := s) (Finset.mem_univ i))
    (Finset.le_sup (f := d) (Finset.mem_univ i))
    ((Finset.le_sup (f := H) (Finset.mem_univ i)).trans (Nat.le_add_right _ _))

/-- Full planar input-format uniformity: numerical budgets precede Boolean
tables, every real coefficient/radius/width valuation, all component entries,
and both endpoints. No arbitrary-catalogue or higher-dimensional bound. -/
theorem published_inputFormat_original_joint_readout_cut_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    (s d : ℕ) :
    ∃ N sPath dPath H : ℕ, 2≤H ∧ ∀ b : (Fin s → Bool × Bool) → Bool,
      ∃ D : JointComponentPartition
        (planarBoundedBandFamily (universalPolynomialBooleanSet (Fin 2) s d b)),
        D.count≤N ∧ ∀ i : Fin D.count,
          OriginalJointEndpointCutPathFamily univ (D.part i) sPath dPath H := by
  classical
  obtain ⟨N,hD⟩ := published_uniform_original_joint_buffered_components hCell hHardt hQE s d
  choose D hcount using hD
  have h := fun b => published_original_component_joint_readout_cut_paths hCAD
    hCell.toFiniteConnectedCover hHardt.toHardtTriviality hQE hPiece (D b)
  choose sp dp H hH hpath using h
  refine ⟨N,Finset.univ.sup sp,Finset.univ.sup dp,Finset.univ.sup H+2,by omega,?_⟩
  intro b
  refine ⟨D b,hcount b,?_⟩
  intro i
  exact (hpath b i).mono (Finset.le_sup (f := sp) (Finset.mem_univ b))
    (Finset.le_sup (f := dp) (Finset.mem_univ b))
    ((Finset.le_sup (f := H) (Finset.mem_univ b)).trans (Nat.le_add_right _ _))

end PaperI
