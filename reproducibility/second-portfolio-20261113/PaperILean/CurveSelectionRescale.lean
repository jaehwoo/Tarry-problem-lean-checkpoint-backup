import PaperILean.CurveSelectionGerm
import PaperILean.PolynomialSignPullback

/-! Restrict an actual half-open germ strictly inside its radius, then rescale.
The new target is C union {a}; an ambient-set application retains a in S.
No assertion is made about the excluded endpoint of the original germ. -/

noncomputable section
namespace PaperI
open Set

theorem mul_unitInterval_mem_Ico {ε δ t : ℝ}
    (hδ : 0 ≤ δ) (hδε : δ < ε) (ht : t ∈ Icc (0 : ℝ) 1) :
    δ*t ∈ Ico (0 : ℝ) ε := by
  exact ⟨mul_nonneg hδ ht.1, (mul_le_of_le_one_right hδ ht.2).trans_lt hδε⟩

theorem rescaled_halfOpen_graph_semialgebraic {α : Type*}
    {ε δ : ℝ} {γ : ℝ → α → ℝ} (hδ : 0 ≤ δ) (hδε : δ < ε)
    (hγ : HasPolynomialSignDescription (halfOpenPathGraph ε γ)) :
    HasPolynomialSignDescription (unitPathGraph (fun t => γ (δ*t))) := by
  classical
  let q : Unit ⊕ α → MvPolynomial (Unit ⊕ α) ℝ :=
    Sum.elim (fun _ => MvPolynomial.C δ * MvPolynomial.X (Sum.inl ()))
      (fun i => MvPolynomial.X (Sum.inr i))
  obtain ⟨A,hA⟩ := hasPolynomialSignDescription_polynomial_preimage hγ q
  let T : MvPolynomial (Unit ⊕ α) ℝ := MvPolynomial.X (Sum.inl ())
  have h0 := polynomialSignDetermined_nonneg T
  have h1 := polynomialSignDetermined_nonneg (1-T)
  have hi := polynomialSignDetermined_inter h0 h1
  have h := polynomialSignDetermined_inter hi hA
  have hs : unitPathGraph (fun t => γ (δ*t)) =
      ({x | 0 ≤ MvPolynomial.eval x T} ∩ {x | 0 ≤ MvPolynomial.eval x (1-T)}) ∩
      {x | (fun i => MvPolynomial.eval x (q i)) ∈ halfOpenPathGraph ε γ} := by
    ext x
    have he : (fun i => MvPolynomial.eval x (q i)) =
        Sum.elim (fun _ : Unit => δ*x (Sum.inl ())) (fun i => x (Sum.inr i)) := by
      funext i
      cases i <;> simp [q]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, T, MvPolynomial.eval_X,
      map_sub, map_one, sub_nonneg, he, halfOpenPathGraph_mem_iff,
      unitPathGraph, Set.mem_Icc]
    constructor
    · rintro ⟨ht,hx⟩
      exact ⟨ht, mul_unitInterval_mem_Ico hδ hδε ht, hx⟩
    · rintro ⟨ht,_,hx⟩
      exact ⟨ht,hx⟩
  rw [hs]
  exact ⟨_,h⟩

def SemialgebraicCurveGerm.rescale {α : Type*} {C : Set (α → ℝ)} {a : α → ℝ}
    (g : SemialgebraicCurveGerm C a) (δ : ℝ) : ℝ → α → ℝ :=
  fun t => g.toFun (δ*t)

theorem SemialgebraicCurveGerm.rescale_source {α : Type*}
    {C : Set (α → ℝ)} {a : α → ℝ} (g : SemialgebraicCurveGerm C a) (δ : ℝ) :
    g.rescale δ 0 = a := by simp [SemialgebraicCurveGerm.rescale, g.source]

theorem SemialgebraicCurveGerm.rescale_target {α : Type*}
    {C : Set (α → ℝ)} {a : α → ℝ} (g : SemialgebraicCurveGerm C a) (δ : ℝ) :
    g.rescale δ 1 = g.toFun δ := by simp [SemialgebraicCurveGerm.rescale]

theorem SemialgebraicCurveGerm.rescale_continuousOn {α : Type*}
    {C : Set (α → ℝ)} {a : α → ℝ} (g : SemialgebraicCurveGerm C a)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδε : δ < g.radius) :
    ContinuousOn (g.rescale δ) (Icc (0 : ℝ) 1) := by
  exact g.continuousOn.comp (continuous_const.mul continuous_id).continuousOn
    (fun _ ht => mul_unitInterval_mem_Ico hδ hδε ht)

theorem SemialgebraicCurveGerm.rescale_enters {α : Type*}
    {C : Set (α → ℝ)} {a : α → ℝ} (g : SemialgebraicCurveGerm C a)
    {δ : ℝ} (hδ : 0 < δ) (hδε : δ < g.radius) :
    MapsTo (g.rescale δ) (Ioc (0 : ℝ) 1) C := by
  intro t ht
  exact g.enters ⟨mul_pos hδ ht.1,
    (mul_unitInterval_mem_Ico hδ.le hδε ⟨ht.1.le,ht.2⟩).2⟩

theorem SemialgebraicCurveGerm.rescale_mapsTo {α : Type*}
    {C : Set (α → ℝ)} {a : α → ℝ} (g : SemialgebraicCurveGerm C a)
    {δ : ℝ} (hδ : 0 < δ) (hδε : δ < g.radius) :
    MapsTo (g.rescale δ) (Icc (0 : ℝ) 1) (C ∪ {a}) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hzero | hpos
  · right
    simpa only [← hzero, g.rescale_source] using (mem_singleton a)
  · exact Or.inl (g.rescale_enters hδ hδε ⟨hpos,ht.2⟩)

theorem SemialgebraicCurveGerm.rescale_semialgebraic {α : Type*}
    {C : Set (α → ℝ)} {a : α → ℝ} (g : SemialgebraicCurveGerm C a)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδε : δ < g.radius) :
    HasPolynomialSignDescription (unitPathGraph (g.rescale δ)) :=
  rescaled_halfOpen_graph_semialgebraic hδ hδε g.semialgebraic

def SemialgebraicCurveGerm.toUnitPath {α : Type*}
    {C : Set (α → ℝ)} {a : α → ℝ} (g : SemialgebraicCurveGerm C a)
    (δ : ℝ) (hδ : 0 < δ) (hδε : δ < g.radius) :
    SemialgebraicUnitPath (C ∪ {a}) a (g.toFun δ) where
  toFun := g.rescale δ
  continuousOn := g.rescale_continuousOn hδ.le hδε
  mapsTo := g.rescale_mapsTo hδ hδε
  source := g.rescale_source δ
  target := g.rescale_target δ
  semialgebraic := g.rescale_semialgebraic hδ.le hδε

def SemialgebraicCurveGerm.toAmbientUnitPath {α : Type*}
    {C S : Set (α → ℝ)} {a : α → ℝ} (g : SemialgebraicCurveGerm C a)
    (hCS : C ⊆ S) (ha : a ∈ S) (δ : ℝ) (hδ : 0 < δ) (hδε : δ < g.radius) :
    SemialgebraicUnitPath S a (g.toFun δ) where
  toFun := g.rescale δ
  continuousOn := g.rescale_continuousOn hδ.le hδε
  mapsTo := by
    intro t ht
    rcases g.rescale_mapsTo hδ hδε ht with hC | he
    · exact hCS hC
    · rw [mem_singleton_iff.mp he]
      exact ha
  source := g.rescale_source δ
  target := g.rescale_target δ
  semialgebraic := g.rescale_semialgebraic hδ.le hδε

end PaperI
