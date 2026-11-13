import PaperILean.CylindricalEndpointPathFamilies
import PaperILean.SelectedGraphMeasurability

/-! Joint Borel measurability of the SAME original CAD path, restricted to
its actual parameter domain and closed unit interval. A Borel substitution
does not assert semialgebraicity of the composed parameter graph. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem jointUnitPathGraph_parameterTime_definable
    {ρ κ : Type} [Finite ρ] [Finite κ] {P : Set (ρ → ℝ)}
    {g : (ρ → ℝ) → ℝ → κ → ℝ}
    (hG : HasPolynomialSignDescription (jointUnitPathGraph P g)) :
    (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph (cadPathParameterDomain P)
        (fun v => g (v ∘ Sum.inl) (v (Sum.inr ())))) := by
  let e : ρ ⊕ (Unit ⊕ κ) → (ρ ⊕ Unit) ⊕ κ :=
    Sum.elim (fun r => Sum.inl (Sum.inl r))
      (Sum.elim (fun u => Sum.inl (Sum.inr u)) Sum.inr)
  convert (hasPolynomialSignDescription_definable hG).preimage_comp e using 1
  ext v
  simp only [selectedFunctionGraph,cadPathParameterDomain,jointUnitPathGraph,
    unitPathGraph,mem_setOf_eq,mem_preimage,Function.comp_def,e,
    Sum.elim_inl,Sum.elim_inr,funext_iff]
  constructor
  · rintro ⟨⟨hp,ht⟩,he⟩
    exact ⟨hp,ht,fun i => (he i).symm⟩
  · rintro ⟨hp,ht,he⟩
    exact ⟨⟨hp,ht⟩,fun i => (he i).symm⟩

theorem published_jointUnitPath_measurable
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ κ : Type} [Finite ρ] [Finite κ] {P : Set (ρ → ℝ)}
    {g : (ρ → ℝ) → ℝ → κ → ℝ}
    (hG : HasPolynomialSignDescription (jointUnitPathGraph P g)) :
    Measurable (fun v : P × Icc (0 : ℝ) 1 => g v.1.val v.2.val) := by
  letI : Fintype ρ := Fintype.ofFinite ρ
  letI : Fintype κ := Fintype.ofFinite κ
  have hm := published_measurable_selected_function hQE hHardt
    (cadPathParameterDomain P) (fun v => g (v ∘ Sum.inl) (v (Sum.inr ())))
    (jointUnitPathGraph_parameterTime_definable hG)
  let e : P × Icc (0 : ℝ) 1 → cadPathParameterDomain P := fun v =>
    ⟨Sum.elim v.1.val (fun _ => v.2.val),v.1.property,v.2.property⟩
  have he : Measurable e := by
    apply Measurable.subtype_mk
    apply measurable_pi_lambda
    intro i
    cases i with
    | inl j =>
      exact (measurable_pi_apply j).comp (measurable_subtype_coe.comp measurable_fst)
    | inr u => exact measurable_subtype_coe.comp measurable_snd
  exact hm.comp he

theorem published_jointUnitPath_measurable_comp
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ κ : Type} [Finite ρ] [Finite κ] {P : Set (ρ → ℝ)}
    {g : (ρ → ℝ) → ℝ → κ → ℝ}
    (hG : HasPolynomialSignDescription (jointUnitPathGraph P g))
    {Ω : Type*} [MeasurableSpace Ω] (q : Ω → P) (hq : Measurable q) :
    Measurable (fun v : Ω × Icc (0 : ℝ) 1 => g (q v.1).val v.2.val) :=
  (published_jointUnitPath_measurable hQE hHardt hG).comp
    ((hq.comp measurable_fst).prodMk measurable_snd)

theorem published_jointEndpointPath_measurable_comp
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ κ : Type} [Finite ρ] [Finite κ] {P : Set (ρ → ℝ)}
    {S : Set ((ρ ⊕ κ) → ℝ)}
    {g : (((ρ ⊕ κ) ⊕ κ) → ℝ) → ℝ → κ → ℝ}
    (hG : HasPolynomialSignDescription (jointUnitPathGraph (cellChainEndpointDomain P S) g))
    {Ω : Type*} [MeasurableSpace Ω] (p : Ω → P) (a b : Ω → κ → ℝ)
    (hp : Measurable p) (ha : Measurable a) (hb : Measurable b)
    (haS : ∀ ω, a ω ∈ projectionFiber S (p ω).val)
    (hbS : ∀ ω, b ω ∈ projectionFiber S (p ω).val) :
    Measurable (fun v : Ω × Icc (0 : ℝ) 1 =>
      g (Sum.elim (Sum.elim (p v.1).val (a v.1)) (b v.1)) v.2.val) := by
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
  exact published_jointUnitPath_measurable_comp hQE hHardt hG q hq

theorem jointRestrictedPath_graph_measurable {Ω κ : Type*}
    [MeasurableSpace Ω] [Fintype κ] (g : Ω → ℝ → κ → ℝ)
    (hg : Measurable (fun v : Ω × Icc (0 : ℝ) 1 => g v.1 v.2.val)) :
    MeasurableSet {v : (Ω × Icc (0 : ℝ) 1) × (κ → ℝ) |
      g v.1.1 v.1.2.val = v.2} :=
  measurableSet_eq_fun (hg.comp measurable_fst) measurable_snd

end PaperI
