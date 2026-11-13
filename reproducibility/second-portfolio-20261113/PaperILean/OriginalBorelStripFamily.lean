import PaperILean.OriginalPreparedPhysicalScale

/-! I1265: joint Borel strip data, exact measurable branch gluing and
pullback. These operations retain the supplied functions and intervals. -/
noncomputable section
namespace PaperI
open Set MeasureTheory

structure OriginalBorelStripFamily (Ω : Type*) [MeasurableSpace Ω] where
  direction : Ω → Fin 4
  graph : Ω × ℝ → ℝ
  left : Ω → ℝ
  right : Ω → ℝ
  reference : Ω → ℝ
  anchor : Ω → Fin 2 → ℝ
  measurable_direction : Measurable direction
  measurable_graph : Measurable graph
  measurable_left : Measurable left
  measurable_right : Measurable right
  measurable_reference : Measurable reference
  measurable_anchor : Measurable anchor

def OriginalBorelStripFamily.strip {Ω : Type*} [MeasurableSpace Ω]
    (B : OriginalBorelStripFamily Ω) (ω : Ω) (W : ℝ) : Set (WithLp 2 (Fin 2 → ℝ)) :=
  signedPlanarStrip (planarDirectionI (B.direction ω)) (planarDirectionSign (B.direction ω))
    (fun x => B.graph (ω,x)) (Icc (B.left ω) (B.right ω)) (W/4)

def OriginalBorelStripFamily.comp {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (B : OriginalBorelStripFamily Ω) (q : Ξ → Ω) (hq : Measurable q) :
    OriginalBorelStripFamily Ξ where
  direction := B.direction ∘ q
  graph := fun v => B.graph (q v.1,v.2)
  left := B.left ∘ q
  right := B.right ∘ q
  reference := B.reference ∘ q
  anchor := B.anchor ∘ q
  measurable_direction := B.measurable_direction.comp hq
  measurable_graph := B.measurable_graph.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  measurable_left := B.measurable_left.comp hq
  measurable_right := B.measurable_right.comp hq
  measurable_reference := B.measurable_reference.comp hq
  measurable_anchor := B.measurable_anchor.comp hq

theorem OriginalBorelStripFamily.strip_comp {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] (B : OriginalBorelStripFamily Ω)
    (q : Ξ → Ω) (hq : Measurable q) (ξ : Ξ) (W : ℝ) :
    (B.comp q hq).strip ξ W=B.strip (q ξ) W := rfl

def OriginalBorelStripFamily.glue {Ω : Type*} [MeasurableSpace Ω]
    (s : Set Ω) (hs : MeasurableSet s)
    (A : OriginalBorelStripFamily s) (B : OriginalBorelStripFamily (sᶜ : Set Ω)) :
    OriginalBorelStripFamily Ω := by
  classical
  have hpair : Measurable (fun v : {v : Ω × ℝ | v.1∈s} =>
      ((⟨v.val.1,v.property⟩ : s),v.val.2)) :=
    (measurable_subtype_coe.fst.subtype_mk).prodMk measurable_subtype_coe.snd
  have hpair' : Measurable (fun v : {v : Ω × ℝ | v.1∈sᶜ} =>
      ((⟨v.val.1,v.property⟩ : (sᶜ : Set Ω)),v.val.2)) :=
    (measurable_subtype_coe.fst.subtype_mk).prodMk measurable_subtype_coe.snd
  exact {
    direction := fun ω => if h : ω∈s then A.direction ⟨ω,h⟩ else B.direction ⟨ω,h⟩
    graph := fun v => if h : v.1∈s then A.graph (⟨v.1,h⟩,v.2) else B.graph (⟨v.1,h⟩,v.2)
    left := fun ω => if h : ω∈s then A.left ⟨ω,h⟩ else B.left ⟨ω,h⟩
    right := fun ω => if h : ω∈s then A.right ⟨ω,h⟩ else B.right ⟨ω,h⟩
    reference := fun ω => if h : ω∈s then A.reference ⟨ω,h⟩ else B.reference ⟨ω,h⟩
    anchor := fun ω => if h : ω∈s then A.anchor ⟨ω,h⟩ else B.anchor ⟨ω,h⟩
    measurable_direction := Measurable.dite A.measurable_direction B.measurable_direction hs
    measurable_graph := Measurable.dite (A.measurable_graph.comp hpair)
      (B.measurable_graph.comp hpair') (hs.preimage measurable_fst)
    measurable_left := Measurable.dite A.measurable_left B.measurable_left hs
    measurable_right := Measurable.dite A.measurable_right B.measurable_right hs
    measurable_reference := Measurable.dite A.measurable_reference B.measurable_reference hs
    measurable_anchor := Measurable.dite A.measurable_anchor B.measurable_anchor hs }

theorem OriginalBorelStripFamily.strip_glue_of_mem {Ω : Type*} [MeasurableSpace Ω]
    (s : Set Ω) (hs : MeasurableSet s) (A : OriginalBorelStripFamily s)
    (B : OriginalBorelStripFamily (sᶜ : Set Ω)) (ω : Ω) (h : ω∈s) (W : ℝ) :
    (A.glue s hs B).strip ω W=A.strip ⟨ω,h⟩ W := by
  classical
  simp [strip,glue,h]

theorem OriginalBorelStripFamily.strip_glue_of_not_mem {Ω : Type*} [MeasurableSpace Ω]
    (s : Set Ω) (hs : MeasurableSet s) (A : OriginalBorelStripFamily s)
    (B : OriginalBorelStripFamily (sᶜ : Set Ω)) (ω : Ω) (h : ω∉s) (W : ℝ) :
    (A.glue s hs B).strip ω W=B.strip ⟨ω,h⟩ W := by
  classical
  simp [strip,glue,h]

theorem continuous_signedPlanarCoordinates (i : Fin 2) (σ : ℝ) :
    Continuous (signedPlanarCoordinates i σ) := by
  have h0 : Continuous (fun p : WithLp 2 (Fin 2 → ℝ) => (WithLp.equiv 2 (Fin 2 → ℝ) p) 0) :=
    (continuous_apply 0).comp (PiLp.continuous_equiv 2 (fun _ : Fin 2 => ℝ))
  have h1 : Continuous (fun p : WithLp 2 (Fin 2 → ℝ) => (WithLp.equiv 2 (Fin 2 → ℝ) p) 1) :=
    (continuous_apply 1).comp (PiLp.continuous_equiv 2 (fun _ : Fin 2 => ℝ))
  change Continuous (fun p : WithLp 2 (Fin 2 → ℝ) => if i=0 then
    (σ*(WithLp.equiv 2 (Fin 2 → ℝ) p) 0,(WithLp.equiv 2 (Fin 2 → ℝ) p) 1) else
    (σ*(WithLp.equiv 2 (Fin 2 → ℝ) p) 1,(WithLp.equiv 2 (Fin 2 → ℝ) p) 0))
  by_cases hi : i=0
  · simp only [hi,↓reduceIte]
    exact (continuous_const.mul h0).prodMk h1
  · simp only [hi,↓reduceIte]
    exact (continuous_const.mul h1).prodMk h0

theorem OriginalBorelStripFamily.measurableSet_joint_strip
    {Ω : Type*} [MeasurableSpace Ω] (B : OriginalBorelStripFamily Ω)
    (W : Ω → ℝ) (hW : Measurable W) :
    MeasurableSet {v : Ω × WithLp 2 (Fin 2 → ℝ) | v.2∈B.strip v.1 (W v.1)} := by
  have hcoord : Measurable (fun v : Ω × WithLp 2 (Fin 2 → ℝ) =>
      signedPlanarCoordinates (planarDirectionI (B.direction v.1))
        (planarDirectionSign (B.direction v.1)) v.2) := by
    have h : Measurable (fun v : WithLp 2 (Fin 2 → ℝ) × Fin 4 =>
        signedPlanarCoordinates (planarDirectionI v.2) (planarDirectionSign v.2) v.1) := by
      apply measurable_from_prod_countable
      intro c
      exact (continuous_signedPlanarCoordinates _ _).measurable
    exact h.comp (measurable_snd.prodMk (B.measurable_direction.comp measurable_fst))
  have heval := B.measurable_graph.comp (measurable_fst.prodMk hcoord.fst)
  have hl := measurableSet_le (B.measurable_left.comp measurable_fst) hcoord.fst
  have hr := measurableSet_le hcoord.fst (B.measurable_right.comp measurable_fst)
  have ht := measurableSet_le (continuous_abs.measurable.comp (hcoord.snd.sub heval))
    ((hW.comp measurable_fst).div_const 4)
  convert (hl.inter hr).inter ht using 1
  ext v
  exact mem_signedPlanarStrip_iff_coordinates _ _ (planarDirection_sign _) _ _ _ _

end PaperI
