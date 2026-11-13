import PaperILean.CompactFamilyMaximum
import PaperILean.SignGraphPowerUpper

/-! I625-638, upper half of (i): the exact maximum has the source's
C*P^C bound provided its finite-sign graph is supplied. The missing real-QE
input is a displayed hypothesis, never a custom axiom. -/

noncomputable section
namespace PaperI

theorem absFamilyMaximum_rpow_upper_of_sign_description
    {X : Type*} [TopologicalSpace X] (K : ℝ → Set X) (g : ℝ → X → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hcompact : ∀ T : ℝ, IsCompact (parameterFamilyWindow K T))
    (hg : ContinuousOn (fun z : ℝ × X => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1})
    (hdesc : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = absFamilyMaximum K g (v (Sum.inl ()))}) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → absFamilyMaximum K g P ≤ C * P ^ C := by
  obtain ⟨C, hC, hb⟩ := sign_graph_rpow_upper (absFamilyMaximum K g)
    (absFamilyMaximum_bounded_window K g hK hne hcompact hg) hdesc
  exact ⟨C, hC, fun P hP => (le_abs_self _).trans (hb P hP)⟩

theorem continuous_family_rpow_upper_of_sign_description
    {X : Type*} [TopologicalSpace X] (K : ℝ → Set X) (g : ℝ → X → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hcompact : ∀ T : ℝ, IsCompact (parameterFamilyWindow K T))
    (hg : ContinuousOn (fun z : ℝ × X => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1})
    (hdesc : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = absFamilyMaximum K g (v (Sum.inl ()))}) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → ∀ x ∈ K P, |g P x| ≤ C * P ^ C := by
  obtain ⟨C, hC, hb⟩ := absFamilyMaximum_rpow_upper_of_sign_description K g hK hne hcompact hg hdesc
  refine ⟨C, hC, ?_⟩
  intro P hP x hx
  obtain ⟨_, _, _, _, hm⟩ := absFamilyMaximum_spec K g hK hne hg P hP
  exact (hm x hx).trans (hb P hP)

theorem polynomially_bounded_family_rpow_upper_of_sign_description
    {ι : Type*} (K : ℝ → Set (ι → ℝ)) (g : ℝ → (ι → ℝ) → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hclosed : ∀ T : ℝ, IsClosed (parameterFamilyWindow K T))
    (A : ℝ) (hA : 0 ≤ A) (N : ℕ)
    (hcoord : ∀ P : ℝ, 2 ≤ P → ∀ x ∈ K P, ∀ i, |x i| ≤ A * P ^ N)
    (hg : ContinuousOn (fun z : ℝ × (ι → ℝ) => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1})
    (hdesc : HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = absFamilyMaximum K g (v (Sum.inl ()))}) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → ∀ x ∈ K P, |g P x| ≤ C * P ^ C := by
  exact continuous_family_rpow_upper_of_sign_description K g hK hne
    (isCompact_parameterFamilyWindow_of_polynomial_coordinates K hclosed A hA N hcoord) hg hdesc

end PaperI

