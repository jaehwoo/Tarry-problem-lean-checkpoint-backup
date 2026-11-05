import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! I625-638: exact maxima and compact bounded-parameter windows. Joint
continuity is restricted to the original family, not to its extrema. -/

noncomputable section
namespace PaperI

def parameterFamilyWindow {X : Type*} (K : ℝ → Set X) (T : ℝ) : Set (ℝ × X) :=
  {z | 2 ≤ z.1 ∧ z.1 ≤ T ∧ z.2 ∈ K z.1}

theorem isCompact_parameterFamilyWindow_of_polynomial_coordinates
    {ι : Type*} (K : ℝ → Set (ι → ℝ))
    (hclosed : ∀ T : ℝ, IsClosed (parameterFamilyWindow K T))
    (A : ℝ) (hA : 0 ≤ A) (N : ℕ)
    (hcoord : ∀ P : ℝ, 2 ≤ P → ∀ x ∈ K P, ∀ i, |x i| ≤ A * P ^ N)
    (T : ℝ) : IsCompact (parameterFamilyWindow K T) := by
  let B : ℝ := A * (max 2 T) ^ N
  apply ((isCompact_Icc : IsCompact (Set.Icc (2 : ℝ) T)).prod
    (isCompact_Icc : IsCompact (Set.Icc (fun _ : ι => -B) (fun _ => B)))).of_isClosed_subset
      (hclosed T)
  intro z hz
  refine ⟨⟨hz.1, hz.2.1⟩, ?_, ?_⟩
  · intro i
    have h := (hcoord z.1 hz.1 z.2 hz.2.2 i).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_trans (by norm_num) hz.1 : 0 ≤ z.1)
          (hz.2.1.trans (le_max_right (2 : ℝ) T)) N) hA)
    exact (abs_le.mp h).1
  · intro i
    have h := (hcoord z.1 hz.1 z.2 hz.2.2 i).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_trans (by norm_num) hz.1 : 0 ≤ z.1)
          (hz.2.1.trans (le_max_right (2 : ℝ) T)) N) hA)
    exact (abs_le.mp h).2

theorem continuous_family_abs_bounded_window {X : Type*} [TopologicalSpace X]
    (K : ℝ → Set X) (g : ℝ → X → ℝ)
    (hcompact : ∀ T : ℝ, IsCompact (parameterFamilyWindow K T))
    (hg : ContinuousOn (fun z : ℝ × X => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1}) (T : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ P : ℝ, 2 ≤ P → P ≤ T → ∀ x ∈ K P, |g P x| ≤ B := by
  by_cases hne : (parameterFamilyWindow K T).Nonempty
  · obtain ⟨z, hz, hmax⟩ := (hcompact T).exists_isMaxOn hne
      (hg.abs.mono (fun _ h => ⟨h.1, h.2.2⟩))
    refine ⟨|g z.1 z.2| + 1, by positivity, ?_⟩
    intro P hP hPT x hx
    exact (hmax (show (P, x) ∈ parameterFamilyWindow K T from ⟨hP, hPT, hx⟩)).trans
      (by linarith)
  · exact ⟨1, by norm_num, fun P hP hPT x hx => False.elim (hne ⟨(P, x), hP, hPT, hx⟩)⟩

theorem csSup_image_eq_of_maximizer {X : Type*} {K : Set X} {f : X → ℝ}
    {x : X} (hx : x ∈ K) (hmax : ∀ y ∈ K, f y ≤ f x) :
    sSup (f '' K) = f x := by
  apply IsGreatest.csSup_eq
  exact ⟨⟨x, hx, rfl⟩, fun _ ⟨y, hy, he⟩ => he ▸ hmax y hy⟩

def absFamilyMaximum {X : Type*} (K : ℝ → Set X) (g : ℝ → X → ℝ) (P : ℝ) : ℝ :=
  sSup ((fun x => |g P x|) '' K P)

theorem absFamilyMaximum_spec {X : Type*} [TopologicalSpace X]
    (K : ℝ → Set X) (g : ℝ → X → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hg : ContinuousOn (fun z : ℝ × X => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1}) (P : ℝ) (hP : 2 ≤ P) :
    ∃ x ∈ K P, absFamilyMaximum K g P = |g P x| ∧
      0 ≤ absFamilyMaximum K g P ∧ ∀ y ∈ K P, |g P y| ≤ absFamilyMaximum K g P := by
  have hc : ContinuousOn (fun x => |g P x|) (K P) :=
    (hg.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => show (P, x) ∈ {z : ℝ × X | 2 ≤ z.1 ∧ z.2 ∈ K z.1} from ⟨hP, hx⟩)).abs
  obtain ⟨x, hx, hmax⟩ := (hK P hP).exists_isMaxOn (hne P hP) hc
  have he : absFamilyMaximum K g P = |g P x| := csSup_image_eq_of_maximizer hx hmax
  exact ⟨x, hx, he, he.symm ▸ abs_nonneg _, he.symm ▸ hmax⟩

theorem absFamilyMaximum_eq_iff {X : Type*} [TopologicalSpace X]
    (K : ℝ → Set X) (g : ℝ → X → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hg : ContinuousOn (fun z : ℝ × X => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1}) (P t : ℝ) (hP : 2 ≤ P) :
    t = absFamilyMaximum K g P ↔ ∃ x ∈ K P, t = |g P x| ∧ ∀ y ∈ K P, |g P y| ≤ t := by
  obtain ⟨x, hx, he, _, hmax⟩ := absFamilyMaximum_spec K g hK hne hg P hP
  constructor
  · rintro rfl
    exact ⟨x, hx, he, hmax⟩
  · rintro ⟨y, hy, ht, hb⟩
    exact le_antisymm (ht.trans_le (hmax y hy)) (he.trans_le (hb x hx))

theorem absFamilyMaximum_bounded_window {X : Type*} [TopologicalSpace X]
    (K : ℝ → Set X) (g : ℝ → X → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hcompact : ∀ T : ℝ, IsCompact (parameterFamilyWindow K T))
    (hg : ContinuousOn (fun z : ℝ × X => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1}) (T : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ P : ℝ, 2 ≤ P → P ≤ T → |absFamilyMaximum K g P| ≤ B := by
  obtain ⟨B, hB, hb⟩ := continuous_family_abs_bounded_window K g hcompact hg T
  refine ⟨B, hB, ?_⟩
  intro P hP hPT
  obtain ⟨x, hx, he, hnonneg, _⟩ := absFamilyMaximum_spec K g hK hne hg P hP
  rw [abs_of_nonneg hnonneg, he]
  exact hb P hP hPT x hx

end PaperI

