import PaperILean.PublishedSemialgebraicCellDecomposition
import Mathlib.Analysis.Convex.Basic

/-! I654, first local step of the original cell-chart route. Interpolate in
the open cube, not in the physical cell. No chart extension to the boundary,
compactness, positive dimension or distinct-endpoint hypothesis is used.
Pre-strategy diagnostics: evidence/checkpoint_109_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set

def cubeAffine {d : ℕ} (u v : openUnitCube d) (t : ℝ) : Fin d → ℝ :=
  fun i => (1 - t) * u.val i + t * v.val i

theorem cubeAffine_mem {d : ℕ} (u v : openUnitCube d) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : cubeAffine u v t ∈ openUnitCube d := by
  intro i
  have h := (convex_Ioo (0 : ℝ) 1) (u.property i) (v.property i)
    (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  simpa only [cubeAffine, smul_eq_mul] using h

def cubeSegment {d : ℕ} (u v : openUnitCube d) (t : Icc (0 : ℝ) 1) :
    openUnitCube d := ⟨cubeAffine u v t.val, cubeAffine_mem u v t.property⟩

theorem cubeSegment_continuous {d : ℕ} (u v : openUnitCube d) :
    Continuous (cubeSegment u v) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.mul continuous_const)

theorem cubeSegment_source {d : ℕ} (u v : openUnitCube d) :
    cubeSegment u v ⟨0, by simp⟩ = u := by
  apply Subtype.ext
  funext i
  simp [cubeSegment, cubeAffine]

theorem cubeSegment_target {d : ℕ} (u v : openUnitCube d) :
    cubeSegment u v ⟨1, by simp⟩ = v := by
  apply Subtype.ext
  funext i
  simp [cubeSegment, cubeAffine]

theorem cubeSegment_same {d : ℕ} (u : openUnitCube d) (t : Icc (0 : ℝ) 1) :
    cubeSegment u u t = u := by
  apply Subtype.ext
  funext i
  change (1 - t.val) * u.val i + t.val * u.val i = u.val i
  ring

theorem cubeSegment_zero_dim (u v : openUnitCube 0) (t : Icc (0 : ℝ) 1) :
    cubeSegment u v t = u := Subsingleton.elim _ _

def cellChartPath {α : Type*} {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C) (a b : C) (t : ℝ) : α → ℝ :=
  if ht : t ∈ Icc (0 : ℝ) 1 then
    (e (cubeSegment (e.symm a) (e.symm b) ⟨t, ht⟩)).val else a.val

theorem cellChartPath_eq {α : Type*} {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C) (a b : C) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cellChartPath e a b t =
      (e (cubeSegment (e.symm a) (e.symm b) ⟨t, ht⟩)).val := by
  simp only [cellChartPath, dif_pos ht]

theorem cellChartPath_continuousOn {α : Type*} {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C) (a b : C) :
    ContinuousOn (cellChartPath e a b) (Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have h := continuous_subtype_val.comp
    (e.continuous.comp (cubeSegment_continuous (e.symm a) (e.symm b)))
  convert h using 1
  funext t
  exact cellChartPath_eq e a b t.property

theorem cellChartPath_mapsTo {α : Type*} {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C) (a b : C) :
    MapsTo (cellChartPath e a b) (Icc (0 : ℝ) 1) C := by
  intro t ht
  rw [cellChartPath_eq e a b ht]
  exact (e _).property

theorem cellChartPath_source {α : Type*} {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C) (a b : C) : cellChartPath e a b 0 = a.val := by
  rw [cellChartPath_eq e a b (by simp), cubeSegment_source, e.apply_symm_apply]

theorem cellChartPath_target {α : Type*} {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C) (a b : C) : cellChartPath e a b 1 = b.val := by
  rw [cellChartPath_eq e a b (by simp), cubeSegment_target, e.apply_symm_apply]

theorem cellChartPath_same {α : Type*} {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C) (a : C) (t : ℝ) : cellChartPath e a a t = a.val := by
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · rw [cellChartPath_eq e a a ht, cubeSegment_same, e.apply_symm_apply]
  · simp only [cellChartPath, dif_neg ht]

theorem cellChartPath_zero_dim {α : Type*} {C : Set (α → ℝ)}
    (e : openUnitCube 0 ≃ₜ C) (a b : C) (t : ℝ) : cellChartPath e a b t = a.val := by
  have h : a = b := e.symm.injective (Subsingleton.elim _ _)
  subst b
  exact cellChartPath_same e a t

end PaperI
