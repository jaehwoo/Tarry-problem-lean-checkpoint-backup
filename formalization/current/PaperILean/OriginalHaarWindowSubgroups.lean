import PaperILean.OriginalHaarOrbitPolynomial
import PaperILean.PolynomialSignPullbackDegree
import PaperILean.OriginalHaarWindowPivot
import PaperILean.OriginalHaarWindowComponentPaths

/-! The three literal source subgroups and the actual orbit-window format.
No larger class of coordinate-zero sets is asserted to be a subgroup. -/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology

inductive OriginalHaarSubgroup
  | H0 | H3 | H
  deriving DecidableEq

def originalHaarSubgroupSet (K : OriginalHaarSubgroup) : Set (Fin 6 → ℝ) :=
  match K with
  | .H0 => {g | g 4=0 ∧ g 5=0}
  | .H3 => {g | g 3=0 ∧ g 4=0 ∧ g 5=0}
  | .H => {g | g 0=0 ∧ g 5=0}

theorem originalHaarSubgroup_zero : ∀ K, (0:Fin 6 → ℝ) ∈ originalHaarSubgroupSet K := by
  intro K
  cases K <;> simp [originalHaarSubgroupSet]

theorem originalHaarSubgroup_sign_congruence (K : OriginalHaarSubgroup)
    (x y : Fin 6 → ℝ) (h : ∀ i, x i=0 ↔ y i=0) :
    x ∈ originalHaarSubgroupSet K ↔ y ∈ originalHaarSubgroupSet K := by
  cases K
  · exact and_congr (h 4) (h 5)
  · exact and_congr (h 3) (and_congr (h 4) (h 5))
  · exact and_congr (h 0) (h 5)

def originalHaarOrbitWindow {k : ℕ} (K : OriginalHaarSubgroup)
    (F : CoefficientSpace k) (W : Set (CoefficientSpace k)) : Set (Fin 6 → ℝ) :=
  {g | g ∈ originalHaarSubgroupSet K ∧ originalUpperCoefficientPullback F g ∈ W}

/-- The full actual preimage has fixed sign format before every phase
coefficient and every component/coset location. Zero degree is permitted. -/
theorem originalHaarOrbitWindow_bounded_sign_format
    {k : ℕ} (K : OriginalHaarSubgroup) (F : CoefficientSpace k)
    (A : Finset (MvPolynomial (MonomialIndex k) ℝ)) (W : Set (CoefficientSpace k))
    (s D : ℕ) (hAc : A.card ≤ s) (hAd : ∀ q ∈ A, q.totalDegree ≤ D)
    (hAW : PolynomialSignDetermined A W) :
    ∃ B : Finset (MvPolynomial (Fin 6) ℝ), B.card ≤ s+6 ∧
      (∀ q ∈ B, q.totalDegree ≤ max (D*k) 1) ∧
      PolynomialSignDetermined B (originalHaarOrbitWindow K F W) := by
  classical
  obtain ⟨B,hBc,hBd,hB⟩ := polynomial_preimage_bounded_sign_format A W s D k hAc hAd hAW
    (OriginalHaarOrbitPolynomial.orbitPolynomial F)
    (OriginalHaarOrbitPolynomial.orbitPolynomial_degree F)
  let C : Finset (MvPolynomial (Fin 6) ℝ) :=
    B ∪ Finset.univ.image (fun i : Fin 6 => MvPolynomial.X i)
  refine ⟨C,?_,?_,?_⟩
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add hBc (by
      exact Finset.card_image_le.trans (by simp)))
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (hBd p hp).trans (Nat.le_max_left _ _)
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
      exact (by simp : (MvPolynomial.X i : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1).trans
        (Nat.le_max_right _ _)
  · intro x y hxy
    have hg : x ∈ originalHaarSubgroupSet K ↔ y ∈ originalHaarSubgroupSet K := by
      apply originalHaarSubgroup_sign_congruence K x y
      intro i
      simpa only [MvPolynomial.eval_X] using
        (hxy (MvPolynomial.X i) (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))).1
    have ho := hB x y (fun p hp => hxy p (Finset.mem_union_left _ hp))
    simp only [OriginalHaarOrbitPolynomial.orbitPolynomial_eval] at ho
    exact and_congr hg ho

/-- A constant coordinate of a path on the closed unit interval has zero
actual derivative at every interior point. -/
theorem originalHaar_path_coordinate_derivative_zero
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1)
    (hg : HasDerivAt g v t) (i : Fin 6)
    (hz : ∀ s ∈ Icc (0:ℝ) 1, g s i=0) : v i=0 := by
  have he : (fun s => g s i) =ᶠ[𝓝 t] (fun _ => (0:ℝ)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hz s ⟨hs.1.le,hs.2.le⟩
  exact (hasDerivAt_pi.mp hg i).unique ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he)

/-- The source physical body remains in the Lie algebra of its specified
subgroup. This is checked for all three actual coordinate constraints. -/
theorem originalHaar_path_body_mem_subgroup
    (K : OriginalHaarSubgroup) (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ)
    (ht : t ∈ Ioo (0:ℝ) 1) (hg : HasDerivAt g v t)
    (hK : ∀ s ∈ Icc (0:ℝ) 1, g s ∈ originalHaarSubgroupSet K) :
    originalAffineBodyCoordinates (g t) v ∈ originalHaarSubgroupSet K := by
  have hgt := hK t ⟨ht.1.le,ht.2.le⟩
  cases K
  · have hv4 := originalHaar_path_coordinate_derivative_zero g v t ht hg 4 (fun s hs => (hK s hs).1)
    have hv5 := originalHaar_path_coordinate_derivative_zero g v t ht hg 5 (fun s hs => (hK s hs).2)
    simp [originalHaarSubgroupSet,originalAffineBodyCoordinates,hv4,hv5]
  · have hv3 := originalHaar_path_coordinate_derivative_zero g v t ht hg 3 (fun s hs => (hK s hs).1)
    have hv4 := originalHaar_path_coordinate_derivative_zero g v t ht hg 4 (fun s hs => (hK s hs).2.1)
    have hv5 := originalHaar_path_coordinate_derivative_zero g v t ht hg 5 (fun s hs => (hK s hs).2.2)
    simp [originalHaarSubgroupSet,originalAffineBodyCoordinates,hv3,hv4,hv5]
  · have hv0 := originalHaar_path_coordinate_derivative_zero g v t ht hg 0 (fun s hs => (hK s hs).1)
    have hv5 := originalHaar_path_coordinate_derivative_zero g v t ht hg 5 (fun s hs => (hK s hs).2)
    simp [originalHaarSubgroupSet,originalAffineBodyCoordinates,hv0,hv5]

end PaperI
