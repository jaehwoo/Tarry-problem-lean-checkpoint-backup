import PaperILean.OriginalJointPathCertificate
import PaperILean.BoundedPolynomialTuple

/-! I649/I654/I1263/I1265: the same original joint CAD construction on
universal coefficients. Bounds precede all tables, coefficients, radii,
widths, component indices and labels. No arbitrary-catalogue bound is asserted. -/
noncomputable section
namespace PaperI
open Set

theorem published_inputFormat_original_joint_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (s d : ℕ) :
    ∃ N sPath dPath K M : ℕ, ∀ b : (Fin s → Bool × Bool) → Bool,
      ∃ D : JointComponentPartition
        (planarBoundedBandFamily (universalPolynomialBooleanSet (Fin 2) s d b)),
        D.count ≤ N ∧ ∀ i : Fin D.count,
          OriginalJointLargePathCertificate D i sPath dPath K M := by
  classical
  obtain ⟨N,hD⟩ := published_uniform_original_joint_buffered_components hCell hHardt hQE s d
  choose D hcount using hD
  have h := fun b => published_originalJointLargePathCertificates hCAD
    hCell.toFiniteConnectedCover hHardt hQE hNash hPiece (D b)
  choose sp dp k m hpath using h
  refine ⟨N,Finset.univ.sup sp,Finset.univ.sup dp,
    Finset.univ.sup k,Finset.univ.sup m,?_⟩
  intro b
  refine ⟨D b,hcount b,fun i => (hpath b i).mono ?_ ?_ ?_ ?_⟩
  · exact Finset.le_sup (f := sp) (Finset.mem_univ b)
  · exact Finset.le_sup (f := dp) (Finset.mem_univ b)
  · exact Finset.le_sup (f := k) (Finset.mem_univ b)
  · exact Finset.le_sup (f := m) (Finset.mem_univ b)

/-- A fixed table and the original bounded-degree tuple represent its actual
fiber exactly, including all zero/repeated polynomials and degree drops. -/
theorem originalUniversalPolynomialSet_fiber (s d : ℕ)
    (P : Fin s → MvPolynomial (Fin 2) ℝ) (hP : ∀ i, (P i).totalDegree ≤ d)
    (b : (Fin s → Bool × Bool) → Bool) :
    projectionFiber (universalPolynomialBooleanSet (Fin 2) s d b)
      (polynomialFamilyCoefficients d P) = polynomialBooleanSet P b :=
  universalPolynomialBooleanSet_fiber s d P hP b

/-- At-most format is represented by a padded tuple and one finite table.
This is an exact existence statement, not a claim that arbitrary pointwise
choices of encodings are measurable. -/
theorem original_bounded_format_universal_representation
    (s d : ℕ) (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ))
    (hcard : A.card ≤ s) (hdegree : ∀ q ∈ A, q.totalDegree ≤ d)
    (hS : PolynomialSignDetermined A S) :
    ∃ (P : Fin s → MvPolynomial (Fin 2) ℝ) (b : (Fin s → Bool × Bool) → Bool),
      (∀ i, (P i).totalDegree ≤ d) ∧
      S = projectionFiber (universalPolynomialBooleanSet (Fin 2) s d b)
        (polynomialFamilyCoefficients d P) := by
  obtain ⟨P,hP,hPS⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s d hcard hdegree hS
  obtain ⟨b,hb⟩ := polynomialSignDetermined_exists_universal_fiber s d P hP S hPS
  exact ⟨P,b,hP,hb⟩

/-- The same budgets cover every set of at most the stated input format.
The universal joint maps are constructed before the individual set is given. -/
theorem published_boundedFormat_original_joint_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (s d : ℕ) :
    ∃ N sPath dPath K M : ℕ,
      ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
        A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ d) → PolynomialSignDetermined A S →
        ∃ (P : Fin s → MvPolynomial (Fin 2) ℝ) (b : (Fin s → Bool × Bool) → Bool)
          (D : JointComponentPartition
            (planarBoundedBandFamily (universalPolynomialBooleanSet (Fin 2) s d b))),
          (∀ j, (P j).totalDegree ≤ d) ∧
          S = projectionFiber (universalPolynomialBooleanSet (Fin 2) s d b)
            (polynomialFamilyCoefficients d P) ∧ D.count ≤ N ∧
          ∀ i : Fin D.count, OriginalJointLargePathCertificate D i sPath dPath K M := by
  obtain ⟨N,sp,dp,K,M,h⟩ := published_inputFormat_original_joint_paths
    hCAD hCell hHardt hQE hNash hPiece s d
  refine ⟨N,sp,dp,K,M,?_⟩
  intro A S hcard hdegree hS
  obtain ⟨P,b,hP,hS⟩ := original_bounded_format_universal_representation s d A S hcard hdegree hS
  obtain ⟨D,hcount,hpaths⟩ := h b
  exact ⟨P,b,D,hP,hS,hcount,hpaths⟩

end PaperI
