import PaperILean.PublishedScalarMonotonicity
import Mathlib.Analysis.Analytic.Constructions

/-! Qualitative one-dimensional Nash regularity as an accepted published input.
Source: Fernando--Gamboa--Ruiz, JEMS 16 (2014), 537--570, Section 2.4.1--2
(printed page 545), with Nash analyticity in Section 2.7 (printed page 546).
The non-Nash locus of a semialgebraic function on an affine Nash manifold is
semialgebraic of codimension at least one; on an open real interval it is finite.
This supplies no format-uniform count. No inhabitant or global axiom is added.
Pre-strategy diagnostics: checkpoint_107_scalar_analytic_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set

structure PublishedOneVariableNashRegularity : Prop where
  finite_nonanalytic_locus : ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    HasPolynomialSignDescription (openScalarGraph f a b) →
      ∃ C : Finset ℝ, (∀ c ∈ C, c ∈ Ioo a b) ∧
        ∀ x ∈ Ioo a b, x ∉ C → AnalyticAt ℝ f x

/-- Coordinate exceptional sets are united before choosing an evaluation point. -/
theorem published_finite_family_analytic_exceptions
    (hNash : PublishedOneVariableNashRegularity)
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hG : ∀ i, HasPolynomialSignDescription (openScalarGraph (f i) a b)) :
    ∃ C : Finset ℝ, (∀ c ∈ C, c ∈ Ioo a b) ∧
      ∀ x ∈ Ioo a b, x ∉ C → ∀ i, AnalyticAt ℝ (f i) x := by
  classical
  choose C hC hA using fun i => hNash.finite_nonanalytic_locus (f i) a b hab (hG i)
  refine ⟨Finset.univ.biUnion C, ?_, ?_⟩
  · intro c hc
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hc
    exact hC i c hi
  · intro x hx hxC i
    apply hA i x hx
    intro hxi
    exact hxC (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hxi⟩)

theorem published_finite_pi_analytic_exceptions
    (hNash : PublishedOneVariableNashRegularity)
    {ι : Type*} [Fintype ι] (f : ℝ → ι → ℝ) (a b : ℝ) (hab : a < b)
    (hG : ∀ i, HasPolynomialSignDescription (openScalarGraph (fun t => f t i) a b)) :
    ∃ C : Finset ℝ, (∀ c ∈ C, c ∈ Ioo a b) ∧
      ∀ x ∈ Ioo a b, x ∉ C → AnalyticAt ℝ f x := by
  obtain ⟨C,hC,hA⟩ := published_finite_family_analytic_exceptions
    hNash (fun i t => f t i) a b hab hG
  exact ⟨C,hC,fun x hx hxc => AnalyticAt.pi (hA x hx hxc)⟩

/-- Adding endpoints gives genuine analytic open pieces. It does not bound the
number of those pieces uniformly over a family. -/
theorem published_finite_pi_analytic_cut_intervals
    (hNash : PublishedOneVariableNashRegularity)
    {ι : Type*} [Fintype ι] (f : ℝ → ι → ℝ) (a b : ℝ) (hab : a < b)
    (hG : ∀ i, HasPolynomialSignDescription (openScalarGraph (fun t => f t i) a b)) :
    ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
      ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
        AnalyticOnNhd ℝ f (Ioo u v) := by
  classical
  obtain ⟨E,hE,hA⟩ := published_finite_pi_analytic_exceptions hNash f a b hab hG
  let C := insert a (insert b E)
  have hC : ∀ c ∈ C, c ∈ Icc a b := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨le_rfl,hab.le⟩
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨hab.le,le_rfl⟩
    exact ⟨(hE c hc).1.le,(hE c hc).2.le⟩
  refine ⟨C,by simp [C],by simp [C],hC,?_⟩
  intro u hu v hv _ hgap x hx
  exact hA x ⟨(hC u hu).1.trans_lt hx.1,hx.2.trans_le (hC v hv).2⟩
    (fun hxE => hgap x (by simp [C,hxE]) hx)

end PaperI
