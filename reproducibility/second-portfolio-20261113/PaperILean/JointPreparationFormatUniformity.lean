import PaperILean.JointOriginalPreparation

/-! The original universal polynomial-sign encoding makes the preceding
joint preparation constants depend only on s,D,N. The Boolean table ranges
over a finite type; coefficients and Borel substitutions come afterward.
This does not assert a Borel coefficient encoding for an arbitrary family
whose graph is merely known pointwise to have bounded format. -/
noncomputable section
namespace PaperI
open Set
open scoped BigOperators

theorem published_inputFormat_joint_original_preparation
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    (s D N : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∃ K : ℕ, 0<K ∧
      ∀ B : (Fin s → Bool × Bool) → Bool,
      ∀ (Ω : Type*) [MeasurableSpace Ω]
      (p : Ω → (Fin s × (Fin 2 → Fin (D+1))) → ℝ) (f : Ω → ℝ → ℝ) (a b : Ω → ℝ),
      Measurable p → Measurable a → Measurable b → (∀ ω, a ω<b ω) →
      (∀ ω, ∀ x∈Icc (a ω) (b ω), ∀ y,
        Sum.elim (p ω) ![x,y]∈universalPolynomialBooleanSet (Fin 2) s D B ↔ y=f ω x) →
      (∀ ω, LipschitzOnWith 1 (f ω) (Icc (a ω) (b ω))) →
      ∃ u v : Ω → ℝ, Measurable u ∧ Measurable v ∧ ∀ ω,
        u ω<v ω ∧ Icc (u ω) (v ω)⊆Icc (a ω) (b ω) ∧
        (b ω-a ω)/(K : ℝ)≤v ω-u ω ∧ AnalyticOnNhd ℝ (f ω) (Icc (u ω) (v ω)) ∧
        (∀ x∈Icc (u ω) (v ω), ∀ n≤N,
          |iteratedDeriv n (fun q => f ω q-f ω (a ω)) x|≤C*(b ω-a ω)/(b ω-a ω)^n) ∧
        (∀ x∈Icc (u ω) (v ω), ∀ n, 0<n → n≤N →
          |iteratedDeriv n (f ω) x|≤C*(b ω-a ω)/(b ω-a ω)^n) := by
  classical
  have h := fun B : (Fin s → Bool × Bool) → Bool =>
    published_joint_original_lipschitz_prepared_interval hDD hCAD hCell hHardt hQE hPiece
      (universalPolynomialBooleanSet (Fin 2) s D B)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s D B)) N
  choose C hC K hK hprep using h
  let CT : ℝ := 1+∑ B, C B
  let KT : ℕ := 1+∑ B, K B
  have hCnonneg (B) : 0≤C B := zero_le_one.trans (hC B)
  have hCT : 1≤CT := le_add_of_nonneg_right (Finset.sum_nonneg (fun B _ => hCnonneg B))
  have hKT : 0<KT := by dsimp [KT]; omega
  have hCb (B) : C B≤CT := by
    have hsum := Finset.single_le_sum (fun B _ => hCnonneg B) (Finset.mem_univ B)
    dsimp [CT]
    linarith
  have hKb (B) : K B≤KT := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ B)).trans (Nat.le_add_left _ _)
  refine ⟨CT,hCT,KT,hKT,?_⟩
  intro B Ω inst p f a b hp ha hb hab hrep hLip
  obtain ⟨u,v,hu,hv,hout⟩ := hprep B Ω p f a b hp ha hb hab hrep hLip
  refine ⟨u,v,hu,hv,?_⟩
  intro ω
  obtain ⟨huv,hsub,hlen,hA,hcenter,hgeom⟩ := hout ω
  have hlen' : (b ω-a ω)/(KT : ℝ)≤v ω-u ω :=
    (div_le_div_of_nonneg_left (sub_nonneg.mpr (hab ω).le)
      (by exact_mod_cast hK B) (by exact_mod_cast hKb B)).trans hlen
  have hscale (n : ℕ) : C B*(b ω-a ω)/(b ω-a ω)^n≤CT*(b ω-a ω)/(b ω-a ω)^n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hCb B) (sub_nonneg.mpr (hab ω).le))
      (pow_nonneg (sub_nonneg.mpr (hab ω).le) n)
  exact ⟨huv,hsub,hlen',hA,fun x hx n hn => (hcenter x hx n hn).trans (hscale n),
    fun x hx n hn hN => (hgeom x hx n hn hN).trans (hscale n)⟩

/-- The already established macroscopic lower span propagates without
changing its interval budget H or the preparation loss K. -/
theorem prepared_interval_macroscopic_length {L ell u v : ℝ} {H K : ℕ}
    (hH : 0<H) (hK : 0<K) (hspan : L/(4*(H : ℝ))≤ell)
    (hretained : ell/(K : ℝ)≤v-u) : L/(4*(H : ℝ)*(K : ℝ))≤v-u := by
  have hKr : 0<(K : ℝ) := by exact_mod_cast hK
  have hHr : 0<(H : ℝ) := by exact_mod_cast hH
  calc
    _ = (L/(4*(H : ℝ)))/(K : ℝ) := by rw [div_div]
    _ ≤ ell/(K : ℝ) := div_le_div_of_nonneg_right hspan hKr.le
    _ ≤ v-u := hretained

end PaperI
