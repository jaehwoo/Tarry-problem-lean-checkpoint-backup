import PaperILean.FiniteDefinableSelection

/-! Exact real-coordinate graph of a finite-valued selector. A definable
partition, not arbitrary pointwise choice, supplies joint definability.
The common-format theorem below concerns one supplied finite family only. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def encodedFiniteSelectorGraph {ρ κ ι : Type*} (U : Set (ρ → ℝ))
    (pick : U → ι) (encode : ι → κ → ℝ) : Set ((ρ ⊕ κ) → ℝ) :=
  {z | ∃ hp : z ∘ Sum.inl ∈ U, encode (pick ⟨z ∘ Sum.inl,hp⟩) = z ∘ Sum.inr}

theorem encodedFiniteSelectorGraph_definable {ρ κ ι : Type*} [Fintype κ] [Fintype ι]
    (U : Set (ρ → ℝ)) (pick : U → ι) (encode : ι → κ → ℝ)
    (hfiber : ∀ i, (univ : Set ℝ).Definable Language.ring
      {p : ρ → ℝ | ∃ hp : p ∈ U, pick ⟨p,hp⟩ = i}) :
    (univ : Set ℝ).Definable Language.ring (encodedFiniteSelectorGraph U pick encode) := by
  let T : ι → Set ((ρ ⊕ κ) → ℝ) := fun i =>
    {z | (∃ hp : z ∘ Sum.inl ∈ U, pick ⟨z ∘ Sum.inl,hp⟩ = i) ∧
      ∀ k, z (Sum.inr k) = encode i k}
  have hT : ∀ i, (univ : Set ℝ).Definable Language.ring (T i) := by
    intro i
    have he := realDefinable_finite_all (fun k : κ =>
      realPolynomial_zero_definable
        (MvPolynomial.X (Sum.inr k) - MvPolynomial.C (encode i k) : MvPolynomial (ρ ⊕ κ) ℝ))
    simpa only [T, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
      sub_eq_zero] using (hfiber i).preimage_comp Sum.inl |>.inter he
  have h := Set.definable_finset_biUnion hT Finset.univ
  convert h using 1
  ext z
  simp only [encodedFiniteSelectorGraph, Set.mem_setOf_eq, Set.mem_iUnion,
    Finset.mem_univ, exists_prop, true_and, T]
  constructor
  · rintro ⟨hp,hpicks⟩
    exact ⟨pick ⟨z ∘ Sum.inl,hp⟩,⟨hp,rfl⟩,fun k => (congrFun hpicks k).symm⟩
  · rintro ⟨i,⟨hp,hi⟩,he⟩
    refine ⟨hp,?_⟩
    rw [hi]
    exact funext (fun k => (he k).symm)

theorem published_encodedFiniteSelectorGraph_semialgebraic
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ ι : Type} [Finite ρ] [Fintype κ] [Fintype ι]
    (U : Set (ρ → ℝ)) (pick : U → ι) (encode : ι → κ → ℝ)
    (hfiber : ∀ i, (univ : Set ℝ).Definable Language.ring
      {p : ρ → ℝ | ∃ hp : p ∈ U, pick ⟨p,hp⟩ = i}) :
    HasPolynomialSignDescription (encodedFiniteSelectorGraph U pick encode) :=
  hQE.finite_sign_description _ (encodedFiniteSelectorGraph_definable U pick encode hfiber)

theorem finite_sign_descriptions_common_format {α ι : Type*} [Fintype ι]
    (D : ι → Set (α → ℝ)) (hD : ∀ i, HasPolynomialSignDescription (D i)) :
    ∃ s d : ℕ, ∀ i, ∃ A : Finset (MvPolynomial α ℝ),
      A.card ≤ s ∧ (∀ v ∈ A, v.totalDegree ≤ d) ∧ PolynomialSignDetermined A (D i) := by
  classical
  choose A hA using hD
  refine ⟨Finset.univ.sup (fun i => (A i).card),
    Finset.univ.sup (fun i => (A i).sup MvPolynomial.totalDegree),?_⟩
  intro i
  exact ⟨A i,Finset.le_sup (f := fun i => (A i).card) (Finset.mem_univ i),
    fun v hv => (Finset.le_sup (f := MvPolynomial.totalDegree) hv).trans
      (Finset.le_sup (f := fun i => (A i).sup MvPolynomial.totalDegree) (Finset.mem_univ i)),hA i⟩

end PaperI
