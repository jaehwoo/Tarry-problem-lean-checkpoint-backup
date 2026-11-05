import PaperILean.CylindricalLiftPaths

/-! Restricted joint graph algebra, including total real inversion. These are
proved definability closures, not new published inputs. Zero denominators have
their Lean field value zero; geometric use separately proves positivity. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

abbrev CADScalarDefinable {α : Type} (U : Set (α → ℝ)) (f : (α → ℝ) → ℝ) : Prop :=
  (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U (fun x (_ : Unit) => f x))

theorem cad_selectedGraph_coordinates {α β γ : Type} [Finite α] [Finite β] [Finite γ]
    {U : Set (α → ℝ)} {f : (α → ℝ) → β → ℝ}
    (hf : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph U f))
    (e : γ → β) : (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph U (fun x => f x ∘ e)) := by
  letI : Fintype γ := Fintype.ofFinite γ
  exact cad_selectedGraph_comp hf (coordinateSectionGraph_definable
    (Set.definable_univ : (univ : Set ℝ).Definable Language.ring (univ : Set (β → ℝ))) e)
    (fun _ _ => mem_univ _)

theorem CADScalarDefinable.add {α : Type} [Finite α] {U : Set (α → ℝ)}
    {f g : (α → ℝ) → ℝ} (hf : CADScalarDefinable U f) (hg : CADScalarDefinable U g) :
    CADScalarDefinable U (fun x => f x+g x) := by
  simpa only [one_mul,add_zero] using cad_selectedGraph_affineCombination hf hg 1 1 0

theorem CADScalarDefinable.sub {α : Type} [Finite α] {U : Set (α → ℝ)}
    {f g : (α → ℝ) → ℝ} (hf : CADScalarDefinable U f) (hg : CADScalarDefinable U g) :
    CADScalarDefinable U (fun x => f x-g x) := by
  simpa only [one_mul,neg_one_mul,add_zero,sub_eq_add_neg] using
    cad_selectedGraph_affineCombination hf hg 1 (-1) 0

theorem CADScalarDefinable.mul {α : Type} [Finite α] {U : Set (α → ℝ)}
    {f g : (α → ℝ) → ℝ} (hf : CADScalarDefinable U f) (hg : CADScalarDefinable U g) :
    CADScalarDefinable U (fun x => f x*g x) := by
  have hp := cad_selectedGraph_polynomial
    (Set.definable_univ : (univ : Set ℝ).Definable Language.ring (univ : Set ((Unit ⊕ Unit) → ℝ)))
    (fun _ : Unit => MvPolynomial.X (Sum.inl ()) * MvPolynomial.X (Sum.inr ()))
  have h := cad_selectedGraph_comp (cad_selectedGraph_pair hf hg) hp (fun _ _ => mem_univ _)
  simpa only [Function.comp_def,map_mul,MvPolynomial.eval_X,Sum.elim_inl,Sum.elim_inr] using h

theorem cad_inverse_graph_definable : CADScalarDefinable (univ : Set (Unit → ℝ))
    (fun x => (x ())⁻¹) := by
  let X : MvPolynomial (Unit ⊕ Unit) ℝ := MvPolynomial.X (Sum.inl ())
  let Y : MvPolynomial (Unit ⊕ Unit) ℝ := MvPolynomial.X (Sum.inr ())
  have h := ((realPolynomial_zero_definable X).inter (realPolynomial_zero_definable Y)).union
    ((realPolynomial_zero_definable X).compl.inter (realPolynomial_zero_definable (X*Y-1)))
  convert h using 1
  ext v
  simp only [selectedFunctionGraph,mem_setOf_eq,mem_univ,true_and,funext_iff,
    Function.comp_def,mem_union,mem_inter_iff,mem_compl_iff,map_sub,map_mul,map_one,
    X,Y,MvPolynomial.eval_X,sub_eq_zero]
  change (∀ _ : Unit, (v (Sum.inl ()))⁻¹ = v (Sum.inr ())) ↔
    (v (Sum.inl ()) = 0 ∧ v (Sum.inr ()) = 0) ∨
      (v (Sum.inl ()) ≠ 0 ∧ v (Sum.inl ())*v (Sum.inr ()) = 1)
  simp only [forall_const]
  by_cases hx : v (Sum.inl ()) = 0
  · simp [hx,eq_comm]
  · constructor
    · intro hv
      exact Or.inr ⟨hx,by rw [← hv]; exact mul_inv_cancel₀ hx⟩
    · intro hv
      rcases hv with hv | hv
      · exact (hx hv.1).elim
      rw [inv_eq_one_div]
      apply (div_eq_iff hx).mpr
      nlinarith [hv.2]

theorem CADScalarDefinable.inv {α : Type} [Finite α] {U : Set (α → ℝ)}
    {f : (α → ℝ) → ℝ} (hf : CADScalarDefinable U f) :
    CADScalarDefinable U (fun x => (f x)⁻¹) :=
  cad_selectedGraph_comp hf cad_inverse_graph_definable (fun _ _ => mem_univ _)

theorem CADScalarDefinable.div {α : Type} [Finite α] {U : Set (α → ℝ)}
    {f g : (α → ℝ) → ℝ} (hf : CADScalarDefinable U f) (hg : CADScalarDefinable U g) :
    CADScalarDefinable U (fun x => f x/g x) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

theorem CADScalarDefinable.mix {α : Type} [Finite α] {U : Set (α → ℝ)}
    {t f g : (α → ℝ) → ℝ} (ht : CADScalarDefinable U t)
    (hf : CADScalarDefinable U f) (hg : CADScalarDefinable U g) :
    CADScalarDefinable U (fun x => cadMix (t x) (f x) (g x)) := by
  have hU := selectedFunctionGraph_domain_definable U (fun x (_ : Unit) => t x) ht
  have h1 : CADScalarDefinable U (fun _ => 1) := cad_selectedGraph_const hU (fun _ => 1)
  exact ((h1.sub ht).mul hf).add (ht.mul hg)

end PaperI
