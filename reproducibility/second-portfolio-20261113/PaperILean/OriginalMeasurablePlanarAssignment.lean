import PaperILean.OriginalUniformPlanarPackage

/-! I1245/I1265: a total measurable map for the SAME original assignment.
The value none is used when no component is assigned, including empty catalogues.
The proof uses the countable component/scale target, not countability of labels.
-/
noncomputable section
namespace PaperI
open Set MeasureTheory

def originalPlanarAssignment {Ω Λ ρ : Type*} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (j : Λ) : Option (ℤ × Fin D.count) := by
  classical
  exact if h : ∃ q : ℤ × Fin D.count,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2
    then some (Classical.choose h) else none

theorem originalPlanarAssignment_eq_some_iff
    {Ω Λ ρ : Type*} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (j : Λ)
    (hcomplete : active ω j → ∃! q : ℤ × Fin D.count,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2)
    (q : ℤ × Fin D.count) :
    originalPlanarAssignment D active param radius point ω j=some q ↔
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2 := by
  classical
  unfold originalPlanarAssignment
  by_cases h : ∃ q : ℤ × Fin D.count,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2
  · simp only [dif_pos h,Option.some.injEq]
    constructor
    · intro heq
      exact heq ▸ Classical.choose_spec h
    · intro hq
      obtain ⟨q0,_,hu⟩ := hcomplete hq.1.1
      exact (hu _ (Classical.choose_spec h)).trans (hu q hq).symm
  · simp only [dif_neg h]
    constructor
    · intro heq
      cases heq
    · intro hq
      exact (h ⟨q,hq⟩).elim

theorem originalPlanarAssignment_eq_none_iff
    {Ω Λ ρ : Type*} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (j : Λ)
    (hcomplete : active ω j → ∃! q : ℤ × Fin D.count,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2) :
    originalPlanarAssignment D active param radius point ω j=none ↔ ¬active ω j := by
  classical
  constructor
  · intro hn ha
    obtain ⟨q,hq,_⟩ := hcomplete ha
    have hs := (originalPlanarAssignment_eq_some_iff D active param radius point ω j hcomplete q).mpr hq
    rw [hn] at hs
    cases hs
  · intro ha
    have hn : ¬∃ q : ℤ × Fin D.count,
        originalDyadicComponentAssigned D active param radius point ω j q.1 q.2 :=
      fun ⟨_,hq⟩ => ha hq.1.1
    simp only [originalPlanarAssignment,dif_neg hn]

theorem originalPlanarAssignment_measurable
    (hQE : PublishedRealSemialgebraicity)
    {Ω Λ : Type*} {ρ : Type} [MeasurableSpace Ω] [Finite ρ]
    {G : Set ((ρ ⊕ Fin 2) → ℝ)} (hG : HasPolynomialSignDescription G)
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ)
    (ha : ∀ j, MeasurableSet {ω | active ω j}) (hp : Measurable param)
    (hT : Measurable radius) (hx : ∀ j, Measurable (fun ω => point ω j))
    (hcomplete : ∀ ω j, active ω j → ∃! q : ℤ × Fin D.count,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2)
    (j : Λ) : Measurable[_, ⊤] (fun ω => originalPlanarAssignment D active param radius point ω j) := by
  letI : MeasurableSpace (Option (ℤ × Fin D.count)) := ⊤
  apply measurable_to_countable'
  intro q
  cases q with
  | none =>
    convert (ha j).compl using 1
    ext ω
    exact originalPlanarAssignment_eq_none_iff D active param radius point ω j (hcomplete ω j)
  | some q =>
    convert measurableSet_originalDyadicComponentAssigned hQE
      (hasPolynomialSignDescription_definable hG) D active param radius point ha hp hT hx j q.1 q.2 using 1
    ext ω
    exact originalPlanarAssignment_eq_some_iff D active param radius point ω j (hcomplete ω j) q

def originalAssignedPlanarStrip {Ω Λ : Type*} {ρ : Type}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (B : Fin D.count → OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (j : Λ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  match originalPlanarAssignment D active param radius point ω j with
  | none => ∅
  | some q => (B q.2).strip (originalDyadicPositiveParameters param radius q.1 ω) ((2:ℝ)^q.1)

theorem originalAssignedPlanarStrip_eq
    {Ω Λ : Type*} {ρ : Type} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (B : Fin D.count → OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (j : Λ)
    (hcomplete : active ω j → ∃! q : ℤ × Fin D.count,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2)
    (q : ℤ × Fin D.count)
    (hq : originalDyadicComponentAssigned D active param radius point ω j q.1 q.2) :
    originalAssignedPlanarStrip D B active param radius point ω j=
      (B q.2).strip (originalDyadicPositiveParameters param radius q.1 ω) ((2:ℝ)^q.1) := by
  unfold originalAssignedPlanarStrip
  rw [(originalPlanarAssignment_eq_some_iff D active param radius point ω j hcomplete q).mpr hq]

theorem originalAssignedPlanarStrip_joint_measurable
    (hQE : PublishedRealSemialgebraicity)
    {Ω Λ : Type*} {ρ : Type} [MeasurableSpace Ω] [Finite ρ]
    {G : Set ((ρ ⊕ Fin 2) → ℝ)} (hG : HasPolynomialSignDescription G)
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (B : Fin D.count → OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ)
    (ha : ∀ j, MeasurableSet {ω | active ω j}) (hp : Measurable param)
    (hT : Measurable radius) (hx : ∀ j, Measurable (fun ω => point ω j))
    (hcomplete : ∀ ω j, active ω j → ∃! q : ℤ × Fin D.count,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2)
    (j : Λ) :
    MeasurableSet {v : Ω × EuclideanSpace ℝ (Fin 2) |
      v.2∈originalAssignedPlanarStrip D B active param radius point v.1 j} := by
  have hs := originalPlanarAssignment_measurable hQE hG D active param radius point ha hp hT hx hcomplete j
  have heq : {v : Ω × EuclideanSpace ℝ (Fin 2) |
      v.2∈originalAssignedPlanarStrip D B active param radius point v.1 j}=
      ⋃ q : ℤ × Fin D.count,
        {v | originalPlanarAssignment D active param radius point v.1 j=some q} ∩
        {v | v.2∈(B q.2).strip (originalDyadicPositiveParameters param radius q.1 v.1) ((2:ℝ)^q.1)} := by
    ext v
    simp only [mem_setOf_eq,mem_iUnion,mem_inter_iff]
    cases h : originalPlanarAssignment D active param radius point v.1 j <;>
      simp [originalAssignedPlanarStrip,h]
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  exact ((hs (MeasurableSpace.measurableSet_top (s := {some q}))).preimage measurable_fst).inter
    (originalDyadicCommonStrip_measurable (B q.2) param radius q.1 hp hT)

theorem OriginalDyadicPackingBounds.active_finite
    {Ω Λ ρ : Type*} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    {D : JointComponentPartition (planarBoundedBandFamily G)}
    {active : Ω → Λ → Prop} {param : Ω → ρ → ℝ} {radius : Ω → ℝ}
    {point : Ω → Λ → Fin 2 → ℝ} {ω : Ω} {m : ℕ} {P mass : ℝ}
    (h : OriginalDyadicPackingBounds D active param radius point ω m P mass) :
    {j | active ω j}.Finite := by
  let Q := {q : ℤ × Fin D.count // ∃ j,
    originalDyadicComponentAssigned D active param radius point ω j q.1 q.2}
  letI : Finite Q := h.2.1
  have heq : {j | active ω j}=⋃ q : Q,
      {j | originalDyadicComponentAssigned D active param radius point ω j q.val.1 q.val.2} := by
    ext j
    simp only [mem_setOf_eq,mem_iUnion]
    constructor
    · intro hj
      obtain ⟨q,hq,_⟩ := h.1 j hj
      exact ⟨⟨q,j,hq⟩,hq⟩
    · rintro ⟨q,hq⟩
      exact hq.1.1
  rw [heq]
  exact Set.finite_iUnion (fun q : Q => (h.2.2.2 q.val.1 q.val.2).1)

end PaperI
