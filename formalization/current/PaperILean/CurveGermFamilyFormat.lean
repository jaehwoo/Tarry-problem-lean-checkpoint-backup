import PaperILean.CurveGermFamilyRescale
import PaperILean.PolynomialSignPullbackDegree
import PaperILean.PolynomialFiberFormat

/-! Explicit format bounds for rescaling a supplied joint germ graph.
The output bounds depend only on the supplied cardinality and degree bounds,
and therefore precede all polynomial coefficients, parameters and cutoffs.
This does not construct a joint graph from pointwise curve selection. -/

noncomputable section
namespace PaperI
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
attribute [local instance 2000] Classical.typeDecidableEq

theorem jointGermRescaleMap_totalDegree_le {ρ α : Type*}
    (i : ρ ⊕ (Unit ⊕ α)) :
    (jointGermRescaleMap i).totalDegree ≤ 2 := by
  rcases i with i | (u | i)
  · simp [jointGermRescaleMap]
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simp
  · simp [jointGermRescaleMap]

theorem polynomialFamily_unitInterval_bounds {κ : Type*}
    (i : κ) (B : Finset (MvPolynomial κ ℝ)) (s D : ℕ)
    (hBc : B.card ≤ s) (hBd : ∀ q ∈ B, q.totalDegree ≤ D) :
    (({MvPolynomial.X i} ∪ {1-MvPolynomial.X i}) ∪ B).card ≤ s+2 ∧
      ∀ q ∈ ({MvPolynomial.X i} ∪ {1-MvPolynomial.X i}) ∪ B,
        q.totalDegree ≤ max D 1 := by
  let T : MvPolynomial κ ℝ := MvPolynomial.X i
  change (({T} ∪ {1-T}) ∪ B).card ≤ s+2 ∧ _
  constructor
  · have hIcard : (({T} : Finset _) ∪ {1-T}).card ≤ 2 := by
      exact (Finset.card_union_le _ _).trans (by simp)
    calc
      _ ≤ (({T} : Finset _) ∪ {1-T}).card + B.card := Finset.card_union_le _ _
      _ ≤ 2+s := Nat.add_le_add hIcard hBc
      _ = s+2 := Nat.add_comm _ _
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rw [Finset.mem_singleton.mp hp]
        exact (by simp : (MvPolynomial.X i : MvPolynomial κ ℝ).totalDegree ≤ 1).trans
          (Nat.le_max_right _ _)
      · rw [Finset.mem_singleton.mp hp]
        have hd : (1-MvPolynomial.X i : MvPolynomial κ ℝ).totalDegree ≤ 1 :=
          (MvPolynomial.totalDegree_sub _ _).trans (by simp)
        exact hd.trans (Nat.le_max_right _ _)
    · exact (hBd p hp).trans (Nat.le_max_left _ _)

theorem jointGermRescaledGraph_bounded_sign_format {ρ α : Type*}
    (A : Finset (MvPolynomial (ρ ⊕ (Unit ⊕ α)) ℝ))
    (G : Set ((ρ ⊕ (Unit ⊕ α)) → ℝ)) (s D : ℕ)
    (hcard : A.card ≤ s) (hdegree : ∀ p ∈ A, p.totalDegree ≤ D)
    (hG : PolynomialSignDetermined A G) :
    ∃ B : Finset (MvPolynomial ((ρ ⊕ Unit) ⊕ (Unit ⊕ α)) ℝ),
      B.card ≤ s + 2 ∧ (∀ p ∈ B, p.totalDegree ≤ max (2 * D) 1) ∧
      PolynomialSignDetermined B (jointGermRescaledGraph G) := by
  let B : Finset (MvPolynomial ((ρ ⊕ Unit) ⊕ (Unit ⊕ α)) ℝ) :=
    A.image (MvPolynomial.bind₁ (@jointGermRescaleMap ρ α))
  have hBc : B.card ≤ s := Finset.card_image_le.trans hcard
  have hBd' : ∀ q ∈ B, q.totalDegree ≤ 2*D := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    calc
      (MvPolynomial.bind₁ (@jointGermRescaleMap ρ α) p).totalDegree
          ≤ p.totalDegree*2 := polynomial_bind_totalDegree_le _ 2
            (@jointGermRescaleMap_totalDegree_le ρ α) p
      _ ≤ D*2 := Nat.mul_le_mul_right 2 (hdegree p hp)
      _ = 2*D := Nat.mul_comm D 2
  obtain ⟨hc,hd⟩ := polynomialFamily_unitInterval_bounds
    (Sum.inr (Sum.inl ()) : (ρ ⊕ Unit) ⊕ (Unit ⊕ α)) B s (2*D) hBc hBd'
  refine ⟨({MvPolynomial.X (Sum.inr (Sum.inl ()))} ∪
    {1-MvPolynomial.X (Sum.inr (Sum.inl ()))}) ∪ B,hc,hd,?_⟩
  intro x y hxy
  have ht0 := realSignEquivalent_nonneg (hxy
    (MvPolynomial.X (Sum.inr (Sum.inl ())))
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))))
  have ht1 := realSignEquivalent_nonneg (hxy
    (1-MvPolynomial.X (Sum.inr (Sum.inl ())))
    (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))))
  simp only [MvPolynomial.eval_X] at ht0
  simp only [map_sub, map_one, MvPolynomial.eval_X, sub_nonneg] at ht1
  have hmem := hG (fun i => MvPolynomial.eval x (jointGermRescaleMap i))
    (fun i => MvPolynomial.eval y (jointGermRescaleMap i)) (by
      intro p hp
      have h := hxy (MvPolynomial.bind₁ (@jointGermRescaleMap ρ α) p)
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
      simpa only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁] using h)
  rw [jointGermRescaleMap_eval, jointGermRescaleMap_eval] at hmem
  exact and_congr (and_congr ht0 ht1) hmem

theorem jointGermRescaledGraph_bounded_fiber_format {ρ α : Type*}
    (A : Finset (MvPolynomial (ρ ⊕ (Unit ⊕ α)) ℝ))
    (G : Set ((ρ ⊕ (Unit ⊕ α)) → ℝ)) (s D : ℕ)
    (hcard : A.card ≤ s) (hdegree : ∀ p ∈ A, p.totalDegree ≤ D)
    (hG : PolynomialSignDetermined A G) (p : ρ → ℝ) (δ : ℝ) :
    ∃ B : Finset (MvPolynomial (Unit ⊕ α) ℝ),
      B.card ≤ s + 2 ∧ (∀ q ∈ B, q.totalDegree ≤ max (2 * D) 1) ∧
      PolynomialSignDetermined B
        (projectionFiber (jointGermRescaledGraph G) (Sum.elim p (fun _ => δ))) := by
  obtain ⟨B,hBc,hBd,hB⟩ :=
    jointGermRescaledGraph_bounded_sign_format A G s D hcard hdegree hG
  exact projectionFiber_has_bounded_sign_format (Sum.elim p (fun _ => δ)) B
    (jointGermRescaledGraph G) (s+2) (max (2*D) 1) hBc hBd hB

theorem halfOpenPathGraphFamily_bounded_rescale_format {ρ α : Type*}
    (P : Set (ρ → ℝ)) (ε : (ρ → ℝ) → ℝ) (γ : (ρ → ℝ) → ℝ → α → ℝ)
    (A : Finset (MvPolynomial (ρ ⊕ (Unit ⊕ α)) ℝ)) (s D : ℕ)
    (hcard : A.card ≤ s) (hdegree : ∀ q ∈ A, q.totalDegree ≤ D)
    (hG : PolynomialSignDetermined A (halfOpenPathGraphFamily P ε γ)) :
    ∀ p ∈ P, ∀ δ : ℝ, 0 ≤ δ → δ < ε p →
      ∃ B : Finset (MvPolynomial (Unit ⊕ α) ℝ),
        B.card ≤ s + 2 ∧ (∀ q ∈ B, q.totalDegree ≤ max (2 * D) 1) ∧
        PolynomialSignDetermined B (unitPathGraph (fun t => γ p (δ*t))) := by
  intro p hp δ hδ hδε
  simpa only [halfOpenPathGraphFamily_rescaled_fiber P ε γ hp hδ hδε] using
    jointGermRescaledGraph_bounded_fiber_format A (halfOpenPathGraphFamily P ε γ)
      s D hcard hdegree hG p δ

/-- For each supplied joint graph of format (s,D), the same numeric output
bounds work for all points and all strictly interior cutoffs. -/
theorem semialgebraicCurveGerm_family_bounded_rescale_format {ρ α : Type*}
    (P : Set (ρ → ℝ)) (C : (ρ → ℝ) → Set (α → ℝ)) (a : (ρ → ℝ) → α → ℝ)
    (g : ∀ p, SemialgebraicCurveGerm (C p) (a p))
    (A : Finset (MvPolynomial (ρ ⊕ (Unit ⊕ α)) ℝ)) (s D : ℕ)
    (hcard : A.card ≤ s) (hdegree : ∀ q ∈ A, q.totalDegree ≤ D)
    (hG : PolynomialSignDetermined A
      (halfOpenPathGraphFamily P (fun p => (g p).radius) (fun p => (g p).toFun))) :
    ∀ p ∈ P, ∀ δ : ℝ, 0 < δ → δ < (g p).radius →
      ∃ η : SemialgebraicUnitPath (C p ∪ {a p}) (a p) ((g p).toFun δ),
        η.toFun = (g p).rescale δ ∧
        ∃ B : Finset (MvPolynomial (Unit ⊕ α) ℝ),
          B.card ≤ s + 2 ∧ (∀ q ∈ B, q.totalDegree ≤ max (2 * D) 1) ∧
          PolynomialSignDetermined B (unitPathGraph η.toFun) := by
  intro p hp δ hδ hδε
  refine ⟨(g p).toUnitPath δ hδ hδε,rfl,?_⟩
  exact halfOpenPathGraphFamily_bounded_rescale_format P
    (fun p => (g p).radius) (fun p => (g p).toFun) A s D hcard hdegree hG
      p hp δ hδ.le hδε

/-- This variant requires actual germs only on P; no off-domain extension is
assumed. The joint graph bound remains an explicit supplied hypothesis. -/
theorem curveGermFamily_bounded_unitPaths {ρ α : Type*} (P : Set (ρ → ℝ))
    (C : (ρ → ℝ) → Set (α → ℝ)) (a : (ρ → ℝ) → α → ℝ)
    (g : ∀ p : P, SemialgebraicCurveGerm (C p.val) (a p.val))
    (A : Finset (MvPolynomial (ρ ⊕ (Unit ⊕ α)) ℝ)) (s D : ℕ)
    (hcard : A.card ≤ s) (hdegree : ∀ q ∈ A, q.totalDegree ≤ D)
    (hG : PolynomialSignDetermined A (curveGermFamilyGraph P C a g)) :
    ∀ p : P, ∀ δ : ℝ, 0 < δ → δ < (g p).radius →
      ∃ η : SemialgebraicUnitPath (C p.val ∪ {a p.val}) (a p.val) ((g p).toFun δ),
        η.toFun = (g p).rescale δ ∧
        ∃ B : Finset (MvPolynomial (Unit ⊕ α) ℝ),
          B.card ≤ s + 2 ∧ (∀ q ∈ B, q.totalDegree ≤ max (2 * D) 1) ∧
          PolynomialSignDetermined B (unitPathGraph η.toFun) := by
  intro p δ hδ hδε
  refine ⟨(g p).toUnitPath δ hδ hδε,rfl,?_⟩
  simpa only [curveGermFamilyGraph_rescaled_fiber P C a g p hδ.le hδε] using
    jointGermRescaledGraph_bounded_fiber_format A (curveGermFamilyGraph P C a g)
      s D hcard hdegree hG p.val δ

end PaperI
