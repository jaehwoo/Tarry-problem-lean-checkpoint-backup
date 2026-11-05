import PaperILean.CylindricalLiftPaths

/-! Actual paths inside a supplied cylindrical tower, preserving its external
base coordinate. This does not assert existence of a finite adapted atlas. -/

noncomputable section
namespace PaperI
open Set

def CylindricalTower.endpointPath {α : Type} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S) :
    (CADVariables α n → ℝ) → (CADVariables α n → ℝ) → ℝ → CADVariables α n → ℝ := by
  induction c with
  | base => exact fun a _ _ => a
  | step previous lift _ ih => exact fun a b => lift.liftPath a b (ih (a ∘ Sum.inl) (b ∘ Sum.inl))

theorem CylindricalTower.endpointPath_projection {α : Type} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S)
    (a b : CADVariables α n → ℝ) (t : ℝ) :
    c.endpointPath a b t ∘ cadBaseCoordinate n = a ∘ cadBaseCoordinate n := by
  induction c with
  | base => rfl
  | step previous lift _ ih => exact ih (a ∘ Sum.inl) (b ∘ Sum.inl)

theorem CylindricalTower.endpointPath_source {α : Type} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S)
    {a : CADVariables α n → ℝ} (ha : a ∈ S) (b : CADVariables α n → ℝ) :
    c.endpointPath a b 0 = a := by
  induction c with
  | base => rfl
  | step previous lift _ ih => exact lift.liftPath_source ha (ih ha.1 _)

theorem CylindricalTower.endpointPath_target {α : Type} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S)
    (a : CADVariables α n → ℝ) {b : CADVariables α n → ℝ} (hb : b ∈ S)
    (hbase : a ∘ cadBaseCoordinate n = b ∘ cadBaseCoordinate n) :
    c.endpointPath a b 1 = b := by
  induction c with
  | base => exact hbase
  | step previous lift _ ih => exact lift.liftPath_target hb (ih _ hb.1 hbase)

theorem CylindricalTower.endpointPath_mem {α : Type} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S)
    {a b : CADVariables α n → ℝ} (ha : a ∈ S) (hb : b ∈ S)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : c.endpointPath a b t ∈ S := by
  induction c with
  | base => exact ha
  | step previous lift _ ih => exact lift.liftPath_mem ha hb ht (ih ha.1 hb.1)

theorem CylindricalTower.endpointPath_continuousOn {α : Type} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S)
    {a b : CADVariables α n → ℝ} (ha : a ∈ S) (hb : b ∈ S) :
    ContinuousOn (c.endpointPath a b) (Icc (0 : ℝ) 1) := by
  induction c with
  | base => exact continuousOn_const
  | step previous lift _ ih =>
    exact lift.liftPath_continuousOn _ _ (ih ha.1 hb.1)
      (fun _ ht => previous.endpointPath_mem ha.1 hb.1 ht)

theorem CylindricalTower.endpointPath_properties {α : Type} {U : Set (α → ℝ)}
    {n : ℕ} {S : Set (CADVariables α n → ℝ)} (c : CylindricalTower U S)
    {a b : CADVariables α n → ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hbase : a ∘ cadBaseCoordinate n = b ∘ cadBaseCoordinate n) :
    ContinuousOn (c.endpointPath a b) (Icc (0 : ℝ) 1) ∧
    MapsTo (c.endpointPath a b) (Icc (0 : ℝ) 1) S ∧
    c.endpointPath a b 0 = a ∧ c.endpointPath a b 1 = b ∧
    ∀ t, c.endpointPath a b t ∘ cadBaseCoordinate n = a ∘ cadBaseCoordinate n :=
  ⟨c.endpointPath_continuousOn ha hb,fun _ ht => c.endpointPath_mem ha hb ht,
    c.endpointPath_source ha b,c.endpointPath_target a hb hbase,
    c.endpointPath_projection a b⟩

end PaperI
