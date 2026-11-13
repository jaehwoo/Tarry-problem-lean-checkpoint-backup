import PaperILean.CylindricalLiftFiberGeometry
import PaperILean.CylindricalCADInput

/-! I1261: a bounded planar cylindrical cell with empty interior is a point or
a continuous graph over a bounded open interval. The first recursive lift is
coordinate 1; the second is coordinate 0. No abstract dimension theorem or
chart-existence conclusion is assumed. -/
noncomputable section
namespace PaperI
open Set

def CylindricalLift.planarFiber {α : Type} {U : Set (α → ℝ)}
    (c : CylindricalLift U) (d : CylindricalLift c.region) (p : α → ℝ) :
    Set (Fin 2 → ℝ) := {x | cadPack 2 p x ∈ d.region}

/-- The distinguished coordinate is the original parameter, ensuring injectivity.
Semialgebraicity and its format are separate properties of the actual image. -/
def IsPlanarIntervalGraph (S : Set (Fin 2 → ℝ)) : Prop :=
  ∃ (i : Fin 2) (a b : ℝ) (γ : ℝ → Fin 2 → ℝ), a < b ∧
    ContinuousOn γ (Ioo a b) ∧ (∀ t ∈ Ioo a b, γ t i = t) ∧ S = γ '' Ioo a b

theorem isOpen_continuousOn_lt {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) {f g : X → ℝ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) :
    IsOpen {x | x ∈ U ∧ f x < g x} := by
  have h := (hg.sub hf).isOpen_inter_preimage hU (isOpen_Ioi (a := (0 : ℝ)))
  convert h using 1
  ext x
  simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ioi, sub_pos]

theorem CylindricalLift.planarFiber_nonempty {α : Type} {U : Set (α → ℝ)}
    (c : CylindricalLift U) (d : CylindricalLift c.region) {p : α → ℝ} (hp : p ∈ U) :
    (c.planarFiber d p).Nonempty :=
  ⟨![d.sample (c.sectionMap p), c.sample p], d.sectionMap_mem (c.sectionMap_mem hp)⟩

theorem CylindricalLift.planarFiber_coord_one_image {α : Type} {U : Set (α → ℝ)}
    (c : CylindricalLift U) (d : CylindricalLift c.region) (p : α → ℝ) :
    (fun x : Fin 2 → ℝ => x 1) '' c.planarFiber d p = c.scalarFiber p := by
  ext t
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx.1
  · intro ht
    exact ⟨![d.sample (Sum.elim p (fun _ : Unit => t)),t], d.sectionMap_mem ht, rfl⟩

theorem CylindricalLift.planarFiber_isOpen_of_two_bands {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) (d : CylindricalLift c.region)
    (p : α → ℝ) (hc : ¬ c.IsGraph) (hd : ¬ d.IsGraph) :
    IsOpen (c.planarFiber d p) := by
  let V : Set (Fin 2 → ℝ) := {x | x 1 ∈ c.scalarFiber p}
  have hV : IsOpen V := (c.scalarFiber_isOpen_of_not_isGraph p hc).preimage (continuous_apply 1)
  have hins : Continuous (fun x : Fin 2 → ℝ => Sum.elim p (fun _ : Unit => x 1)) :=
    (continuous_cadScalarInsert p).comp (continuous_apply 1)
  have hmap : MapsTo (fun x : Fin 2 → ℝ => Sum.elim p (fun _ : Unit => x 1)) V c.region :=
    fun _ hx => hx
  have hf (f : CylindricalBoundary c.region) :
      ContinuousOn (fun x : Fin 2 → ℝ => f.value (Sum.elim p (fun _ : Unit => x 1))) V :=
    f.continuousOn.comp hins.continuousOn hmap
  cases d with
  | graph f => exact (hd trivial).elim
  | between l u h =>
    have hl := isOpen_continuousOn_lt hV (hf l) (continuous_apply 0).continuousOn
    have hu := isOpen_continuousOn_lt hV (continuous_apply 0).continuousOn (hf u)
    convert hl.inter hu using 1
    ext x
    change (x 1 ∈ c.scalarFiber p ∧ _ ∧ _) ↔ ((x 1 ∈ c.scalarFiber p ∧ _) ∧ (x 1 ∈ c.scalarFiber p ∧ _))
    tauto
  | above l => exact isOpen_continuousOn_lt hV (hf l) (continuous_apply 0).continuousOn
  | below u => exact isOpen_continuousOn_lt hV (continuous_apply 0).continuousOn (hf u)
  | whole =>
    convert hV using 1
    ext x
    change (x 1 ∈ c.scalarFiber p ∧ True) ↔ x 1 ∈ c.scalarFiber p
    simp

theorem CylindricalLift.isGraph_or_isGraph_of_empty_interior {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) (d : CylindricalLift c.region)
    {p : α → ℝ} (hp : p ∈ U) (hthin : interior (c.planarFiber d p) = ∅) :
    c.IsGraph ∨ d.IsGraph := by
  by_cases hc : c.IsGraph
  · exact Or.inl hc
  right
  by_contra hd
  have hopen := c.planarFiber_isOpen_of_two_bands d p hc hd
  exact (c.planarFiber_nonempty d hp).ne_empty (hopen.interior_eq.symm.trans hthin)

theorem CylindricalLift.planarFiber_eq_image_of_first_graph {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) (d : CylindricalLift c.region)
    {p : α → ℝ} (hp : p ∈ U) (hc : c.IsGraph) :
    c.planarFiber d p = (fun t : ℝ => ![t,c.sample p]) '' d.scalarFiber (c.sectionMap p) := by
  ext x
  constructor
  · intro hx
    have hx1 : x 1 = c.sample p := by
      have h := hx.1
      change x 1 ∈ c.scalarFiber p at h
      rw [c.scalarFiber_eq_singleton_of_isGraph hp hc] at h
      exact h
    refine ⟨x 0, ?_, ?_⟩
    · change Sum.elim (Sum.elim p (fun _ : Unit => c.sample p)) (fun _ : Unit => x 0) ∈ d.region
      change Sum.elim (Sum.elim p (fun _ : Unit => x 1)) (fun _ : Unit => x 0) ∈ d.region at hx
      simpa only [hx1] using hx
    · funext i
      fin_cases i
      · rfl
      · exact hx1.symm
  · rintro ⟨t,ht,rfl⟩
    exact ht

theorem CylindricalLift.planarFiber_eq_image_of_second_graph {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) (d : CylindricalLift c.region)
    (p : α → ℝ) (hd : d.IsGraph) :
    c.planarFiber d p =
      (fun t : ℝ => ![d.sample (Sum.elim p (fun _ : Unit => t)),t]) '' c.scalarFiber p := by
  ext x
  constructor
  · intro hx
    have hx0 : x 0 = d.sample (Sum.elim p (fun _ : Unit => x 1)) := by
      have h : x 0 ∈ d.scalarFiber (Sum.elim p (fun _ : Unit => x 1)) := hx
      rw [d.scalarFiber_eq_singleton_of_isGraph
        (p := Sum.elim p (fun _ : Unit => x 1)) (show _ ∈ c.region from hx.1) hd] at h
      exact h
    refine ⟨x 1, hx.1, ?_⟩
    funext i
    fin_cases i
    · exact hx0.symm
    · rfl
  · rintro ⟨t,ht,rfl⟩
    exact d.sectionMap_mem ht

theorem CylindricalLift.planarGraphMap_continuousOn {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) (d : CylindricalLift c.region) (p : α → ℝ) :
    ContinuousOn (fun t : ℝ => ![d.sample (Sum.elim p (fun _ : Unit => t)),t]) (c.scalarFiber p) := by
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · exact d.sample_continuousOn.comp (continuous_cadScalarInsert p).continuousOn (fun _ ht => ht)
  · exact continuousOn_id

/-- No isolated points, vertical pieces or finite-endpoint conditions are omitted. -/
theorem CylindricalLift.bounded_thin_planarFiber_cases {α : Type}
    {U : Set (α → ℝ)} (c : CylindricalLift U) (d : CylindricalLift c.region)
    {p : α → ℝ} (hp : p ∈ U) (hthin : interior (c.planarFiber d p) = ∅)
    (hlo : ∀ i : Fin 2, BddBelow ((fun x => x i) '' c.planarFiber d p))
    (hhi : ∀ i : Fin 2, BddAbove ((fun x => x i) '' c.planarFiber d p)) :
    (∃ z, c.planarFiber d p = {z}) ∨ IsPlanarIntervalGraph (c.planarFiber d p) := by
  by_cases hc : c.IsGraph
  · have he := c.planarFiber_eq_image_of_first_graph d hp hc
    have hproj : (fun x : Fin 2 → ℝ => x 0) '' c.planarFiber d p = d.scalarFiber (c.sectionMap p) := by
      rw [he, image_image]
      simp
    have hlow : BddBelow (d.scalarFiber (c.sectionMap p)) := hproj ▸ hlo 0
    have hhigh : BddAbove (d.scalarFiber (c.sectionMap p)) := hproj ▸ hhi 0
    rcases d.bounded_scalarFiber_cases (c.sectionMap_mem hp) hlow hhigh with ⟨a,_,ha⟩ | ⟨a,b,hab,habset⟩
    · left
      exact ⟨![a,c.sample p], by rw [he,ha,image_singleton]⟩
    · right
      refine ⟨0,a,b,(fun t => ![t,c.sample p]),hab,?_,fun _ _ => rfl,?_⟩
      · apply continuousOn_pi.mpr
        intro i
        fin_cases i
        · exact continuousOn_id
        · exact continuousOn_const
      · rw [he,habset]
  · have hd := (c.isGraph_or_isGraph_of_empty_interior d hp hthin).resolve_left hc
    have hproj := c.planarFiber_coord_one_image d p
    have hlow : BddBelow (c.scalarFiber p) := hproj ▸ hlo 1
    have hhigh : BddAbove (c.scalarFiber p) := hproj ▸ hhi 1
    rcases c.bounded_scalarFiber_cases hp hlow hhigh with ⟨_,hg,_⟩ | ⟨a,b,hab,habset⟩
    · exact (hc hg).elim
    · right
      refine ⟨1,a,b,(fun t => ![d.sample (Sum.elim p (fun _ : Unit => t)),t]),hab,?_,fun _ _ => rfl,?_⟩
      · simpa only [habset] using c.planarGraphMap_continuousOn d p
      · rw [c.planarFiber_eq_image_of_second_graph d p hd,habset]

end PaperI
