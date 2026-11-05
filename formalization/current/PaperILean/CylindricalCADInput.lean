import PaperILean.CylindricalGermAttachment

/-! A structural first-band consequence of cylindrical algebraic decomposition.

Source: Basu, Algorithms in Real Algebraic Geometry: A Survey, Definition 2.2
and Theorem 2.4 (author PDF, pp.5-6; BPR Chapter 11). Apply a single CAD to the
finite sign polynomials for P and E, with all parameter coordinates first,
then time, then the n output coordinates, including the time polynomials t
and t-1. On every nonempty base cell in P, the first stack band above zero
has a positive continuous semialgebraic roof at most one. Retain every cell
above that band. Their recursive graph/band data, coverage and compatibility
are precisely the fields below. This is a structural consequence, not a
verbatim source statement. No selector, curve, radius lower bound, derivative,
path-connectedness, or graph-format bound is included in the external input.
No inhabitant of the Prop contract is supplied. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def cadOutputCoordinate {α : Type} : (n : ℕ) → Fin n → CADVariables α n
  | 0 => Fin.elim0
  | n+1 => Fin.cases (Sum.inr ()) (fun i => Sum.inl (cadOutputCoordinate n i))

def cadPack {α : Type} : (n : ℕ) → (α → ℝ) → (Fin n → ℝ) → CADVariables α n → ℝ
  | 0, p, _ => p
  | n+1, p, x => Sum.elim (cadPack n p (fun i => x i.succ)) (fun _ => x 0)

theorem cadPack_base {α : Type} (n : ℕ) :
    ∀ (p : α → ℝ) (x : Fin n → ℝ), cadPack n p x ∘ cadBaseCoordinate n = p := by
  induction n with
  | zero => intro p x; rfl
  | succ n ih =>
    intro p x
    exact ih p (fun i => x i.succ)

theorem cadPack_output {α : Type} (n : ℕ) :
    ∀ (p : α → ℝ) (x : Fin n → ℝ), cadPack n p x ∘ cadOutputCoordinate n = x := by
  induction n with
  | zero => intro p x; funext i; exact Fin.elim0 i
  | succ n ih =>
    intro p x
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (ih p (fun k => x k.succ)) j

structure CylindricalInitialBandDecomposition {ρ : Type} (n : ℕ)
    (P : Set (ρ → ℝ)) (E : Set (CADVariables (ρ ⊕ Unit) n → ℝ)) where
  count : ℕ
  base : Fin count → Set (ρ → ℝ)
  base_definable : ∀ i, (univ : Set ℝ).Definable Language.ring (base i)
  base_nonempty : ∀ i, (base i).Nonempty
  base_subset : ∀ i, base i ⊆ P
  base_cover : ∀ p ∈ P, ∃ i, p ∈ base i
  base_disjoint : Pairwise (fun i j => Disjoint (base i) (base j))
  roof : ∀ i, CylindricalBoundary (base i)
  roof_positive : ∀ i, ∀ p ∈ base i, 0 < (roof i).value p
  roof_le_one : ∀ i, ∀ p ∈ base i, (roof i).value p ≤ 1
  leafCount : Fin count → ℕ
  cell : ∀ i, Fin (leafCount i) → Set (CADVariables (ρ ⊕ Unit) n → ℝ)
  tower : ∀ i j, CylindricalTower (cadInitialBand (base i) (roof i).value) (cell i j)
  cover : ∀ i z, z ∘ cadBaseCoordinate n ∈ cadInitialBand (base i) (roof i).value →
    ∃ j, z ∈ cell i j
  compatible : ∀ i j, cell i j ⊆ E ∨ Disjoint (cell i j) E

structure PublishedCylindricalInitialBandDecomposition : Prop where
  decomposition : ∀ {ρ : Type} [Finite ρ] (n : ℕ)
    (P : Set (ρ → ℝ)) (E : Set (CADVariables (ρ ⊕ Unit) n → ℝ)),
    HasPolynomialSignDescription P → HasPolynomialSignDescription E →
    Nonempty (CylindricalInitialBandDecomposition n P E)

theorem CylindricalInitialBandDecomposition.exists_cell_subset
    {ρ : Type} {n : ℕ} {P : Set (ρ → ℝ)}
    {E : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (d : CylindricalInitialBandDecomposition n P E)
    (hE : ∀ p ∈ P, ∀ t ∈ Ioo (0 : ℝ) 1,
      ∃ x : Fin n → ℝ, cadPack n (Sum.elim p (fun _ : Unit => t)) x ∈ E)
    (i : Fin d.count) : ∃ j, d.cell i j ⊆ E := by
  obtain ⟨p,hp⟩ := d.base_nonempty i
  let t := (d.roof i).value p / 2
  have hpos := d.roof_positive i p hp
  have hone := d.roof_le_one i p hp
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [t]; linarith,by dsimp [t]; linarith⟩
  have htr : t < (d.roof i).value p := by dsimp [t]; linarith
  obtain ⟨x,hx⟩ := hE p (d.base_subset i hp) t ht
  let z := cadPack n (Sum.elim p (fun _ : Unit => t)) x
  have hband : z ∘ cadBaseCoordinate n ∈ cadInitialBand (d.base i) (d.roof i).value := by
    rw [cadPack_base]
    exact ⟨hp,ht.1,htr⟩
  obtain ⟨j,hj⟩ := d.cover i z hband
  rcases d.compatible i j with hsub | hdis
  · exact ⟨j,hsub⟩
  · exact False.elim (Set.disjoint_left.mp hdis hj hx)

end PaperI
