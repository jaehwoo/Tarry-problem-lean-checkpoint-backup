import PaperILean.PolynomialSignDescription

/-! The intrinsic dimension definition in BPR, second edition, printed p.169:
the largest dimension of an open cube admitting an injective semialgebraic
map into the set, with dimension -1 for the empty set. We represent equality
to a dimension relationally. Existence for every semialgebraic set, and the
general cell-maximum theorem, are not asserted by this definition. -/

noncomputable section
namespace PaperI

def openUnitCube (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1}

theorem openUnitCube_nonempty (d : ℕ) : (openUnitCube d).Nonempty :=
  ⟨fun _ => 1 / 2, by intro i; norm_num⟩

theorem openUnitCube_zero_subsingleton : Subsingleton (openUnitCube 0) := inferInstance

/-- The exact graph includes the open-cube domain restriction. -/
def cubeMapGraph {α : Type*} {d : ℕ} (f : openUnitCube d → (α → ℝ)) :
    Set ((Fin d ⊕ α) → ℝ) :=
  {v | ∃ h : (fun i => v (Sum.inl i)) ∈ openUnitCube d,
    f ⟨fun i => v (Sum.inl i), h⟩ = fun i => v (Sum.inr i)}

def HasSemialgebraicCubeInjection {α : Type*} (S : Set (α → ℝ)) (d : ℕ) : Prop :=
  ∃ f : openUnitCube d → (α → ℝ), Function.Injective f ∧
    (∀ x, f x ∈ S) ∧ HasPolynomialSignDescription (cubeMapGraph f)

def HasGeometricSemialgebraicDimension {α : Type*} (S : Set (α → ℝ)) (z : ℤ) : Prop :=
  (z = -1 ∧ S = ∅) ∨
    ∃ d : ℕ, z = (d : ℤ) ∧ HasSemialgebraicCubeInjection S d ∧
      ∀ e : ℕ, HasSemialgebraicCubeInjection S e → e ≤ d

theorem nonempty_of_semialgebraicCubeInjection {α : Type*} {S : Set (α → ℝ)}
    {d : ℕ} (h : HasSemialgebraicCubeInjection S d) : S.Nonempty := by
  obtain ⟨f, _, hf, _⟩ := h
  obtain ⟨x, hx⟩ := openUnitCube_nonempty d
  exact ⟨f ⟨x, hx⟩, hf ⟨x, hx⟩⟩

theorem geometricSemialgebraicDimension_neg_one_iff {α : Type*}
    (S : Set (α → ℝ)) : HasGeometricSemialgebraicDimension S (-1) ↔ S = ∅ := by
  constructor
  · rintro (⟨_, hS⟩ | ⟨d, hd, _⟩)
    · exact hS
    · omega
  · intro hS
    exact Or.inl ⟨rfl, hS⟩

theorem geometricSemialgebraicDimension_empty_iff {α : Type*} (z : ℤ) :
    HasGeometricSemialgebraicDimension (∅ : Set (α → ℝ)) z ↔ z = -1 := by
  constructor
  · rintro (⟨hz, _⟩ | ⟨d, _, hd, _⟩)
    · exact hz
    · exact (nonempty_of_semialgebraicCubeInjection hd).ne_empty rfl |>.elim
  · intro hz
    exact Or.inl ⟨hz, rfl⟩

theorem cubeDimension_eq_zero_of_geometric_dimension_zero {α : Type*}
    {S : Set (α → ℝ)} (h : HasGeometricSemialgebraicDimension S 0)
    {d : ℕ} (hd : HasSemialgebraicCubeInjection S d) : d = 0 := by
  rcases h with ⟨h, _⟩ | ⟨e, he, _, hmax⟩
  · omega
  · have hde := hmax d hd
    omega

theorem geometric_dimension_le_zero_empty_or_zero {α : Type*}
    {S : Set (α → ℝ)} {z : ℤ} (h : HasGeometricSemialgebraicDimension S z)
    (hz : z ≤ 0) : S = ∅ ∨ HasGeometricSemialgebraicDimension S 0 := by
  rcases h with ⟨_, hS⟩ | ⟨d, hd, hinj, hmax⟩
  · exact Or.inl hS
  · have he : d = 0 := by omega
    subst d
    exact Or.inr (Or.inr ⟨0, rfl, hinj, hmax⟩)

theorem nonempty_of_geometric_dimension_zero {α : Type*}
    {S : Set (α → ℝ)} (h : HasGeometricSemialgebraicDimension S 0) : S.Nonempty := by
  rcases h with ⟨h, _⟩ | ⟨d, _, hd, _⟩
  · omega
  · exact nonempty_of_semialgebraicCubeInjection hd

theorem geometricSemialgebraicDimension_unique {α : Type*}
    {S : Set (α → ℝ)} {z w : ℤ}
    (hz : HasGeometricSemialgebraicDimension S z)
    (hw : HasGeometricSemialgebraicDimension S w) : z = w := by
  rcases hz with ⟨hz, hS⟩ | ⟨d, hzd, hd, hdmax⟩
  · rw [hS] at hw
    exact hz.trans ((geometricSemialgebraicDimension_empty_iff w).mp hw).symm
  · rcases hw with ⟨_, hS⟩ | ⟨e, hwe, he, hemax⟩
    · exact ((nonempty_of_semialgebraicCubeInjection hd).ne_empty hS).elim
    · have hde : d = e := Nat.le_antisymm (hemax d hd) (hdmax e he)
      exact hzd.trans ((congrArg (fun n : ℕ => (n : ℤ)) hde).trans hwe.symm)

end PaperI
