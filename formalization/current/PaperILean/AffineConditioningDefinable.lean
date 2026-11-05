import PaperILean.PolynomialSingularValueDefinability
import PaperILean.AttainedMinimumDefinability
import PaperILean.AffineFieldPolynomial
import PaperILean.StoppedStatePolynomialFamily
import PaperILean.AffineConditioningCompact

/-! I3251[578,732): the actual normalized affine-field value and attained-minimum
graphs. The nonnegative square-root witnesses and sorted singular-value graph
retain the literal two action norms, multiplicities, and all physical entries. -/

noncomputable section
open scoped BigOperators Matrix
open FirstOrder
namespace PaperI.AffineConditioning
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- The nonnegative root guard identifies the intended norm value. -/
theorem polynomialSqrtGraph_definable {α : Type*} [Finite α]
    (p t : MvPolynomial α ℝ) (hp : ∀ v : α → ℝ, 0 ≤ MvPolynomial.eval v p) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | MvPolynomial.eval v t = Real.sqrt (MvPolynomial.eval v p)} := by
  have h := (realPolynomial_nonneg_definable t).inter
    (realPolynomial_zero_definable (t ^ 2 - p))
  convert h using 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, map_sub, map_pow, sub_eq_zero]
  constructor
  · intro ht
    rw [ht]
    exact ⟨Real.sqrt_nonneg _, Real.sq_sqrt (hp v)⟩
  · rintro ⟨ht, hsq⟩
    exact ((Real.sqrt_eq_iff_eq_sq (hp v) ht).mpr hsq.symm).symm

theorem polynomialMaxGraph_definable {α : Type*} [Finite α]
    (p q t : MvPolynomial α ℝ) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | MvPolynomial.eval v t =
        max (MvPolynomial.eval v p) (MvPolynomial.eval v q)} := by
  have h₁ := (realPolynomial_le_definable p q).inter
    (realPolynomial_zero_definable (t - q))
  have h₂ := (realPolynomial_le_definable q p).inter
    (realPolynomial_zero_definable (t - p))
  convert h₁.union h₂ using 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, map_sub, sub_eq_zero]
  constructor
  · intro ht
    rcases le_total (MvPolynomial.eval v p) (MvPolynomial.eval v q) with h | h
    · exact Or.inl ⟨h, ht.trans (max_eq_right h)⟩
    · exact Or.inr ⟨h, ht.trans (max_eq_left h)⟩
  · rintro (⟨h, ht⟩ | ⟨h, ht⟩)
    · exact ht.trans (max_eq_right h).symm
    · exact ht.trans (max_eq_left h).symm

/-- The only three existential scalar witnesses are the two literal norms and
the second descending singular value. No diagonalizer is selected continuously. -/
theorem polynomialActionMaximumGraph_definable {α : Type*} [Finite α]
    (p q t : MvPolynomial α ℝ)
    (A : Matrix (Fin 3) (Fin 4) (MvPolynomial α ℝ))
    (hp : ∀ v : α → ℝ, 0 ≤ MvPolynomial.eval v p)
    (hq : ∀ v : α → ℝ, 0 ≤ MvPolynomial.eval v q) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | MvPolynomial.eval v t =
        max (Real.sqrt (MvPolynomial.eval v p) + Real.sqrt (MvPolynomial.eval v q))
          (descendingSingularValues (fun i j => MvPolynomial.eval v (A i j)) (1 : Fin 4))} := by
  let u : Fin 3 → MvPolynomial (α ⊕ Fin 3) ℝ := fun i => MvPolynomial.X (Sum.inr i)
  have hp' := polynomialSqrtGraph_definable (MvPolynomial.rename Sum.inl p) (u 0)
    (fun v => by simpa only [MvPolynomial.eval_rename] using hp (v ∘ Sum.inl))
  have hq' := polynomialSqrtGraph_definable (MvPolynomial.rename Sum.inl q) (u 1)
    (fun v => by simpa only [MvPolynomial.eval_rename] using hq (v ∘ Sum.inl))
  have hs := polynomialSingularValueGraph_definable
    (fun i j => MvPolynomial.rename Sum.inl (A i j)) (u 2) (1 : Fin 4)
  have hm := polynomialMaxGraph_definable (u 0 + u 1) (u 2)
    (MvPolynomial.rename Sum.inl t)
  have h := realDefinable_exists (hp'.inter (hq'.inter (hs.inter hm)))
  convert h using 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, u, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, Function.comp_def, Sum.elim_inl, Sum.elim_inr, map_add]
  constructor
  · intro ht
    refine ⟨![Real.sqrt (MvPolynomial.eval v p), Real.sqrt (MvPolynomial.eval v q),
      descendingSingularValues (fun i j => MvPolynomial.eval v (A i j)) (1 : Fin 4)], ?_⟩
    simpa using ht
  · rintro ⟨w, hpw, hqw, hsw, htw⟩
    simpa only [hpw, hqw, hsw] using htw

abbrev ConditioningJointVariable (k : ℕ) := AugmentedCoordinateIndex k ⊕ FieldIndex
abbrev ConditioningValueVariable (k : ℕ) := (Unit ⊕ ConditioningJointVariable k) ⊕ Unit

def phaseSquarePolynomial (k : ℕ) : MvPolynomial (ConditioningJointVariable k) ℝ :=
  ∑ a : MonomialIndex k, actualActionPolynomial k (Sum.inl a) ^ 2

def physicalSquarePolynomial (k : ℕ) : MvPolynomial (ConditioningJointVariable k) ℝ :=
  (∑ i : Fin 3, actualActionPolynomial k (Sum.inr (Sum.inl i)) ^ 2) +
    ∑ i : Fin 3, ∑ j : Fin 3, actualActionPolynomial k (Sum.inr (Sum.inr (i,j))) ^ 2

theorem eval_phaseSquarePolynomial (k : ℕ) (S : AugmentedState k) (f : FieldIndex → ℝ) :
    MvPolynomial.eval (Sum.elim (augmentedStateCoordinates k S) f) (phaseSquarePolynomial k) =
      coefficientEuclideanNorm (actualAction k S f).1 ^ 2 := by
  simp only [phaseSquarePolynomial, MvPolynomial.eval_sum, map_pow,
    eval_actualActionPolynomial]
  change (∑ a : MonomialIndex k, (actualAction k S f).1 a ^ 2) =
    coefficientEuclideanNorm (actualAction k S f).1 ^ 2
  unfold coefficientEuclideanNorm
  exact (Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).symm

theorem eval_physicalSquarePolynomial (k : ℕ) (S : AugmentedState k) (f : FieldIndex → ℝ) :
    MvPolynomial.eval (Sum.elim (augmentedStateCoordinates k S) f) (physicalSquarePolynomial k) =
      physicalAffineNorm (actualAction k S f).2 ^ 2 := by
  simp only [physicalSquarePolynomial, map_add, MvPolynomial.eval_sum, map_pow,
    eval_actualActionPolynomial]
  change ((∑ i : Fin 3, (actualAction k S f).2.1 i ^ 2) +
    ∑ i : Fin 3, ∑ j : Fin 3, (actualAction k S f).2.2 i j ^ 2) =
    physicalAffineNorm (actualAction k S f).2 ^ 2
  exact (physicalAffineNorm_sq _).symm

theorem phaseSquarePolynomial_nonneg (k : ℕ) (v : ConditioningJointVariable k → ℝ) :
    0 ≤ MvPolynomial.eval v (phaseSquarePolynomial k) := by
  simp only [phaseSquarePolynomial, MvPolynomial.eval_sum, map_pow]
  positivity

theorem physicalSquarePolynomial_nonneg (k : ℕ) (v : ConditioningJointVariable k → ℝ) :
    0 ≤ MvPolynomial.eval v (physicalSquarePolynomial k) := by
  simp only [physicalSquarePolynomial, map_add, MvPolynomial.eval_sum, map_pow]
  positivity

def jointState (k : ℕ) (v : ConditioningJointVariable k → ℝ) : AugmentedState k :=
  (augmentedStateCoordinates k).symm (v ∘ Sum.inl)

def jointField {k : ℕ} (v : ConditioningJointVariable k → ℝ) : FieldIndex → ℝ :=
  v ∘ Sum.inr

theorem joint_coordinates_eta (k : ℕ) (v : ConditioningJointVariable k → ℝ) :
    Sum.elim (augmentedStateCoordinates k (jointState k v)) (jointField v) = v := by
  funext a
  cases a with
  | inl r => simp [jointState]
  | inr j => rfl

theorem jointState_coordinates (k : ℕ) (S : AugmentedState k) (f : FieldIndex → ℝ) :
    jointState k (Sum.elim (augmentedStateCoordinates k S) f) = S := by
  simp [jointState, Function.comp_def]

theorem jointField_coordinates (k : ℕ) (S : AugmentedState k) (f : FieldIndex → ℝ) :
    jointField (Sum.elim (augmentedStateCoordinates k S) f) = f := rfl

theorem gap_graph_definable (k : ℕ) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : ConditioningJointVariable k ⊕ Unit → ℝ |
        v (Sum.inr ()) = gap k (jointState k (v ∘ Sum.inl)) (jointField (v ∘ Sum.inl))} := by
  let p := MvPolynomial.rename (Sum.inl : ConditioningJointVariable k →
    ConditioningJointVariable k ⊕ Unit) (phaseSquarePolynomial k)
  let q := MvPolynomial.rename (Sum.inl : ConditioningJointVariable k →
    ConditioningJointVariable k ⊕ Unit) (physicalSquarePolynomial k)
  let A : Matrix (Fin 3) (Fin 4) (MvPolynomial (ConditioningJointVariable k ⊕ Unit) ℝ) :=
    fun i j => MvPolynomial.X (Sum.inl (Sum.inr (i,j)))
  have h := polynomialActionMaximumGraph_definable p q (MvPolynomial.X (Sum.inr ())) A
    (fun v => by simpa [p, MvPolynomial.eval_rename] using phaseSquarePolynomial_nonneg k (v ∘ Sum.inl))
    (fun v => by simpa [q, MvPolynomial.eval_rename] using physicalSquarePolynomial_nonneg k (v ∘ Sum.inl))
  convert h using 1
  ext v
  have hp := eval_phaseSquarePolynomial k (jointState k (v ∘ Sum.inl)) (jointField (v ∘ Sum.inl))
  have hq := eval_physicalSquarePolynomial k (jointState k (v ∘ Sum.inl)) (jointField (v ∘ Sum.inl))
  rw [joint_coordinates_eta] at hp hq
  simp only [Set.mem_setOf_eq, p, q, A, MvPolynomial.eval_rename, MvPolynomial.eval_X]
  rw [hp, hq, Real.sqrt_sq (coefficientEuclideanNorm_nonneg _),
    Real.sqrt_sq (physicalAffineNorm_nonneg _)]
  rfl

def valueFamily (k : ℕ) : Set (ConditioningValueVariable k → ℝ) :=
  {v | 2 ≤ v (Sum.inl (Sum.inl ())) ∧
    AugmentedTranslationStopped (v (Sum.inl (Sum.inl ())))
      (jointState k (fun r => v (Sum.inl (Sum.inr r)))) ∧
    fieldNorm (jointField (fun r => v (Sum.inl (Sum.inr r)))) = 1 ∧
    v (Sum.inr ()) = gap k (jointState k (fun r => v (Sum.inl (Sum.inr r))))
      (jointField (fun r => v (Sum.inl (Sum.inr r))))}

theorem valueFamily_definable (k : ℕ) :
    (Set.univ : Set ℝ).Definable Language.ring (valueFamily k) := by
  let e : StoppedStateVariable k → ConditioningValueVariable k :=
    Sum.elim (fun _ => Sum.inl (Sum.inl ())) (fun r => Sum.inl (Sum.inr (Sum.inl r)))
  let g : ConditioningJointVariable k ⊕ Unit → ConditioningValueVariable k :=
    Sum.elim (fun r => Sum.inl (Sum.inr r)) Sum.inr
  let unitP : MvPolynomial (ConditioningValueVariable k) ℝ :=
    (∑ j : FieldIndex, MvPolynomial.X (Sum.inl (Sum.inr (Sum.inr j))) ^ 2) - 1
  have hs := (stoppedStateFamily_definable k).preimage_comp e
  have hu := realPolynomial_zero_definable unitP
  have hg := (gap_graph_definable k).preimage_comp g
  convert hs.inter (hu.inter hg) using 1
  ext v
  have hunit : fieldNorm (jointField (fun r => v (Sum.inl (Sum.inr r)))) = 1 ↔
      (∑ j : FieldIndex, v (Sum.inl (Sum.inr (Sum.inr j))) ^ 2) = 1 := by
    have hn := coordinateL2Norm_nonneg (fun j : FieldIndex => v (Sum.inl (Sum.inr (Sum.inr j))))
    have hsq := coordinateL2Norm_sq (fun j : FieldIndex => v (Sum.inl (Sum.inr (Sum.inr j))))
    change coordinateL2Norm (fun j : FieldIndex => v (Sum.inl (Sum.inr (Sum.inr j)))) = 1 ↔ _
    constructor <;> intro h <;> nlinarith
  simp only [valueFamily, stoppedStateFamily, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_preimage, e, g, unitP, MvPolynomial.eval_sum, map_sub, map_pow,
    MvPolynomial.eval_X, map_one, sub_eq_zero, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, and_assoc]
  rw [hunit]
  rfl

theorem attained_graph_iff (k : ℕ) (R t : ℝ) :
    Sum.elim (fun _ : Unit => R) (fun _ : Unit => t) ∈
      attainedFiberMinimumGraph (valueFamily k) ↔
      2 ≤ R ∧ t = minimum k R := by
  have h := attainedFiberMinimumGraph_function_iff
    (fun (p : Unit → ℝ) (x : ConditioningJointVariable k → ℝ) =>
      2 ≤ p () ∧ AugmentedTranslationStopped (p ()) (jointState k x) ∧
        fieldNorm (jointField x) = 1)
    (fun (_ : Unit → ℝ) (x : ConditioningJointVariable k → ℝ) =>
      gap k (jointState k x) (jointField x))
    (fun _ => R) t
  simp only [and_assoc] at h
  change (Sum.elim (fun _ : Unit => R) (fun _ : Unit => t) ∈
    attainedFiberMinimumGraph (valueFamily k) ↔ _) at h
  rw [h]
  constructor
  · rintro ⟨x, hR, hS, hf, ht, hmin⟩
    refine ⟨hR, (minimum_eq_iff k R t hR).mpr
      ⟨jointState k x, jointField x, hS, hf, ht, ?_⟩⟩
    intro T g hT hg
    have hc : 2 ≤ R ∧ AugmentedTranslationStopped R
        (jointState k (Sum.elim (augmentedStateCoordinates k T) g)) ∧
        fieldNorm (jointField (Sum.elim (augmentedStateCoordinates k T) g)) = 1 := by
      simpa only [jointState_coordinates, jointField_coordinates] using ⟨hR, hT, hg⟩
    simpa only [jointState_coordinates, jointField_coordinates] using
      hmin (Sum.elim (augmentedStateCoordinates k T) g) hc
  · rintro ⟨hR, ht⟩
    obtain ⟨S, f, hS, hf, he, hmin⟩ := (minimum_eq_iff k R t hR).mp ht
    refine ⟨Sum.elim (augmentedStateCoordinates k S) f, hR, ?_, ?_, ?_, ?_⟩
    · simpa only [jointState_coordinates] using hS
    · simpa only [jointField_coordinates] using hf
    · simpa only [jointState_coordinates, jointField_coordinates] using he
    · intro y hy
      exact hmin (jointState k y) (jointField y) hy.2.1 hy.2.2

theorem minimum_graph_definable (k : ℕ) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = minimum k (v (Sum.inl ()))} := by
  have h := attainedFiberMinimumGraph_definable (valueFamily_definable k)
  convert h using 1
  ext v
  have he : Sum.elim (fun _ : Unit => v (Sum.inl ()))
      (fun _ : Unit => v (Sum.inr ())) = v := by
    funext a
    rcases a with ⟨⟩ | ⟨⟩ <;> rfl
  simpa only [he, Set.mem_setOf_eq] using
    (attained_graph_iff k (v (Sum.inl ())) (v (Sum.inr ()))).symm

end PaperI.AffineConditioning
