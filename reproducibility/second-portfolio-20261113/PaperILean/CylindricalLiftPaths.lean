import PaperILean.CylindricalTowerSection

/-! Explicit endpoint interpolation in one supplied cylindrical lift.
Between cells are interpolated in normalized vertical coordinates, never by
physical straight chords. Denominator positivity is used only at the endpoints.
The prospective screens are in evidence/checkpoint_118_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set

def cadMix (t a b : ℝ) : ℝ := (1-t)*a+t*b

theorem cadMix_zero (a b : ℝ) : cadMix 0 a b = a := by simp [cadMix]

theorem cadMix_one (a b : ℝ) : cadMix 1 a b = b := by simp [cadMix]

theorem cadMix_pos {t a b : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : 0 < a) (hb : 0 < b) : 0 < cadMix t a b := by
  have h1 : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  have h2 := mul_nonneg h1 (le_of_lt ha)
  have h3 := mul_nonneg ht.1 (le_of_lt hb)
  by_cases h : t = 0
  · simpa [h,cadMix] using ha
  · have h4 := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h)) hb
    dsimp [cadMix]
    linarith

theorem cadMix_mem_Ioo {t a b : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    cadMix t a b ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨cadMix_pos ht ha.1 hb.1,?_⟩
  have h := cadMix_pos ht (sub_pos.mpr ha.2) (sub_pos.mpr hb.2)
  dsimp [cadMix] at h ⊢
  nlinarith

theorem cadMix_continuous (a b : ℝ) : Continuous (fun t => cadMix t a b) := by
  exact ((continuous_const.sub continuous_id).mul continuous_const).add
    (continuous_id.mul continuous_const)

def CylindricalLift.interpolate {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) (a b : (α ⊕ Unit) → ℝ) (x : α → ℝ) (t : ℝ) : ℝ :=
  match c with
  | .graph f => f.value x
  | .between l u _ => l.value x + (u.value x-l.value x) *
      cadMix t ((a (Sum.inr ())-l.value (a ∘ Sum.inl)) /
        (u.value (a ∘ Sum.inl)-l.value (a ∘ Sum.inl)))
      ((b (Sum.inr ())-l.value (b ∘ Sum.inl)) /
        (u.value (b ∘ Sum.inl)-l.value (b ∘ Sum.inl)))
  | .above l => l.value x + cadMix t
      (a (Sum.inr ())-l.value (a ∘ Sum.inl))
      (b (Sum.inr ())-l.value (b ∘ Sum.inl))
  | .below u => u.value x - cadMix t
      (u.value (a ∘ Sum.inl)-a (Sum.inr ()))
      (u.value (b ∘ Sum.inl)-b (Sum.inr ()))
  | .whole => cadMix t (a (Sum.inr ())) (b (Sum.inr ()))

def CylindricalLift.liftPath {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) (a b : (α ⊕ Unit) → ℝ)
    (γ : ℝ → α → ℝ) (t : ℝ) : (α ⊕ Unit) → ℝ :=
  Sum.elim (γ t) (fun _ => c.interpolate a b (γ t) t)

theorem CylindricalLift.liftPath_projection {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) (a b : (α ⊕ Unit) → ℝ)
    (γ : ℝ → α → ℝ) (t : ℝ) : c.liftPath a b γ t ∘ Sum.inl = γ t := rfl

theorem CylindricalLift.interpolate_source {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) {a : (α ⊕ Unit) → ℝ} (ha : a ∈ c.region)
    (b : (α ⊕ Unit) → ℝ) : c.interpolate a b (a ∘ Sum.inl) 0 = a (Sum.inr ()) := by
  cases c with
  | graph f => exact ha.2.symm
  | between l u h =>
    have hd : u.value (a ∘ Sum.inl)-l.value (a ∘ Sum.inl) ≠ 0 :=
      ne_of_gt (sub_pos.mpr (h _ ha.1))
    simp only [interpolate,cadMix_zero]
    field_simp
    <;> simp_all
    <;> ring
  | above l => simp only [interpolate,cadMix_zero]; ring
  | below u => simp only [interpolate,cadMix_zero]; ring
  | whole => exact cadMix_zero _ _

theorem CylindricalLift.interpolate_target {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) (a : (α ⊕ Unit) → ℝ)
    {b : (α ⊕ Unit) → ℝ} (hb : b ∈ c.region) :
    c.interpolate a b (b ∘ Sum.inl) 1 = b (Sum.inr ()) := by
  cases c with
  | graph f => exact hb.2.symm
  | between l u h =>
    have hd : u.value (b ∘ Sum.inl)-l.value (b ∘ Sum.inl) ≠ 0 :=
      ne_of_gt (sub_pos.mpr (h _ hb.1))
    simp only [interpolate,cadMix_one]
    field_simp
    <;> simp_all
    <;> ring
  | above l => simp only [interpolate,cadMix_one]; ring
  | below u => simp only [interpolate,cadMix_one]; ring
  | whole => exact cadMix_one _ _

theorem CylindricalLift.liftPath_source {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) {a b : (α ⊕ Unit) → ℝ} (ha : a ∈ c.region)
    {γ : ℝ → α → ℝ} (hγ : γ 0 = a ∘ Sum.inl) : c.liftPath a b γ 0 = a := by
  funext i
  cases i with
  | inl i => exact congrFun hγ i
  | inr i =>
    change c.interpolate a b (γ 0) 0 = _
    rw [hγ,c.interpolate_source ha b]

theorem CylindricalLift.liftPath_target {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) {a b : (α ⊕ Unit) → ℝ} (hb : b ∈ c.region)
    {γ : ℝ → α → ℝ} (hγ : γ 1 = b ∘ Sum.inl) : c.liftPath a b γ 1 = b := by
  funext i
  cases i with
  | inl i => exact congrFun hγ i
  | inr i =>
    change c.interpolate a b (γ 1) 1 = _
    rw [hγ,c.interpolate_target a hb]

theorem CylindricalLift.liftPath_mem {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) {a b : (α ⊕ Unit) → ℝ}
    (ha : a ∈ c.region) (hb : b ∈ c.region) {γ : ℝ → α → ℝ}
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hγ : γ t ∈ S) :
    c.liftPath a b γ t ∈ c.region := by
  cases c with
  | graph f => exact ⟨hγ,rfl⟩
  | between l u h =>
    have hn (v : (α ⊕ Unit) → ℝ) (hv : v ∈ (CylindricalLift.between l u h).region) :
        (v (Sum.inr ())-l.value (v ∘ Sum.inl)) /
          (u.value (v ∘ Sum.inl)-l.value (v ∘ Sum.inl)) ∈ Ioo (0 : ℝ) 1 := by
      have hd := sub_pos.mpr (h _ hv.1)
      refine ⟨div_pos (sub_pos.mpr hv.2.1) hd,(div_lt_one hd).mpr ?_⟩
      linarith [hv.2.2]
    have hw := cadMix_mem_Ioo ht (hn a ha) (hn b hb)
    have hd := sub_pos.mpr (h _ hγ)
    refine ⟨hγ,?_,?_⟩
    · change l.value (γ t) < l.value (γ t) + (u.value (γ t)-l.value (γ t))*_
      exact lt_add_of_pos_right _ (mul_pos hd hw.1)
    · change l.value (γ t) + (u.value (γ t)-l.value (γ t))*_ < u.value (γ t)
      nlinarith [mul_pos hd (sub_pos.mpr hw.2)]
  | above l =>
    refine ⟨hγ,?_⟩
    exact lt_add_of_pos_right _ (cadMix_pos ht (sub_pos.mpr ha.2) (sub_pos.mpr hb.2))
  | below u =>
    refine ⟨hγ,?_⟩
    exact sub_lt_self _ (cadMix_pos ht (sub_pos.mpr ha.2) (sub_pos.mpr hb.2))
  | whole => exact ⟨hγ,trivial⟩

theorem CylindricalLift.liftPath_continuousOn {α : Type} {S : Set (α → ℝ)}
    (c : CylindricalLift S) (a b : (α ⊕ Unit) → ℝ) {γ : ℝ → α → ℝ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hmap : MapsTo γ (Icc (0 : ℝ) 1) S) :
    ContinuousOn (c.liftPath a b γ) (Icc (0 : ℝ) 1) := by
  apply continuousOn_pi.mpr
  intro i
  cases i with
  | inl i => exact (continuous_apply i).continuousOn.comp hγ (fun _ _ => mem_univ _)
  | inr i =>
    cases c with
    | graph f => exact f.continuousOn.comp hγ hmap
    | between l u _ =>
      exact (l.continuousOn.comp hγ hmap).add
        (((u.continuousOn.comp hγ hmap).sub (l.continuousOn.comp hγ hmap)).mul
          (cadMix_continuous _ _).continuousOn)
    | above l => exact (l.continuousOn.comp hγ hmap).add (cadMix_continuous _ _).continuousOn
    | below u => exact (u.continuousOn.comp hγ hmap).sub (cadMix_continuous _ _).continuousOn
    | whole => exact (cadMix_continuous _ _).continuousOn

end PaperI
