import PaperILean.BoundedTimeProjection
import PaperILean.PlanarMacroscopicArc

/-! The actual selected centerline, not a replacement curve. Only its graph
over the closed projection interval is described; its extension is arbitrary.
All four signed coordinate charts and collapsed time fibers are retained. -/

noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def signedPlanarDecode (i : Fin 2) (σ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun j => if j=i then σ*x 0 else x 1

theorem signedPlanarDecode_coordinates (i k : Fin 2) (hik : i ≠ k)
    (σ : ℝ) (x : Fin 2 → ℝ) :
    signedPlanarDecode i σ x i = σ*x 0 ∧ signedPlanarDecode i σ x k = x 1 := by
  simp [signedPlanarDecode, Ne.symm hik]

theorem signedPlanarDecode_eq_iff (i k : Fin 2) (hik : i ≠ k)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (x y : Fin 2 → ℝ) :
    signedPlanarDecode i σ x = y ↔ x 0 = σ*y i ∧ x 1 = y k := by
  have hj (j : Fin 2) : j=i ∨ j=k := by
    fin_cases i <;> fin_cases k <;> fin_cases j <;> simp_all
  constructor
  · intro h
    have hi := congrFun h i
    have hk := congrFun h k
    simp only [signedPlanarDecode, if_pos rfl, if_neg (Ne.symm hik)] at hi hk
    refine ⟨?_, hk⟩
    rcases hσ with rfl | rfl
    · simpa using hi
    · simpa using congrArg Neg.neg hi
  · rintro ⟨hx, hz⟩
    funext j
    rcases hj j with rfl | rfl
    · simp only [signedPlanarDecode, if_pos rfl, hx]
      rcases hσ with rfl | rfl <;> simp
    · simp [signedPlanarDecode, Ne.symm hik, hz]

def signedPlanarPathSubstitution (i : Fin 2) (σ : ℝ) :
    Unit ⊕ Fin 2 → MvPolynomial (Fin 2 ⊕ Fin 1) ℝ
  | Sum.inl _ => MvPolynomial.X (Sum.inr 0)
  | Sum.inr j => if j=i then MvPolynomial.C σ * MvPolynomial.X (Sum.inl 0)
      else MvPolynomial.X (Sum.inl 1)

theorem signedPlanarPathSubstitution_degree (i : Fin 2) (σ : ℝ)
    (j : Unit ⊕ Fin 2) : (signedPlanarPathSubstitution i σ j).totalDegree ≤ 1 := by
  rcases j with u | j
  · simp [signedPlanarPathSubstitution]
  · simp only [signedPlanarPathSubstitution]
    split_ifs
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · simp

theorem signedPlanarPathSubstitution_eval (i : Fin 2) (σ : ℝ)
    (v : (Fin 2 ⊕ Fin 1) → ℝ) :
    (fun j => MvPolynomial.eval v (signedPlanarPathSubstitution i σ j)) =
      Sum.elim (fun _ => v (Sum.inr 0))
        (signedPlanarDecode i σ (fun j => v (Sum.inl j))) := by
  funext j
  rcases j with u | j
  · simp [signedPlanarPathSubstitution]
  · simp only [signedPlanarPathSubstitution, signedPlanarDecode, Sum.elim_inr]
    split_ifs <;> simp

def signedPlanarRestrictedPath (γ : ℝ → Fin 2 → ℝ)
    (a b : ℝ) (i : Fin 2) (σ : ℝ) : Set ((Fin 2 ⊕ Fin 1) → ℝ) :=
  {v | Sum.elim (fun _ => v (Sum.inr 0))
      (signedPlanarDecode i σ (fun j => v (Sum.inl j))) ∈ unitPathGraph γ ∧
    v (Sum.inr 0) ∈ Icc a b}

theorem signedPlanarRestrictedPath_bounded_format
    (γ : ℝ → Fin 2 → ℝ) (A : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ))
    (s D : ℕ) (hc : A.card ≤ s) (hd : ∀ p ∈ A, p.totalDegree ≤ D)
    (hG : PolynomialSignDetermined A (unitPathGraph γ))
    (a b : ℝ) (i : Fin 2) (σ : ℝ) :
    ∃ B : Finset (MvPolynomial (Fin 2 ⊕ Fin 1) ℝ), B.card ≤ s+2 ∧
      (∀ p ∈ B, p.totalDegree ≤ max D 1) ∧
      PolynomialSignDetermined B (signedPlanarRestrictedPath γ a b i σ) := by
  obtain ⟨B, hBc, hBd, hBG⟩ := polynomial_preimage_bounded_sign_format
    A (unitPathGraph γ) s D 1 hc hd hG (signedPlanarPathSubstitution i σ)
      (signedPlanarPathSubstitution_degree i σ)
  simp only [Nat.mul_one] at hBd
  simp only [signedPlanarPathSubstitution_eval] at hBG
  exact bounded_sign_format_closed_coordinate_restriction B _ s D hBc hBd hBG (Sum.inr 0) a b

def signedPlanarCenterlineGraph (γ : ℝ → Fin 2 → ℝ)
    (a b : ℝ) (i : Fin 2) (σ : ℝ) (h : ℝ → ℝ) : Set (Fin 2 → ℝ) :=
  {x | x 0 ∈ Icc (σ*γ a i) (σ*γ b i) ∧ x 1 = h (x 0)}

theorem signedPlanarCenterlineGraph_eq_projection
    (γ : ℝ → Fin 2 → ℝ) (a b : ℝ) (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ 1) (i k : Fin 2) (hik : i ≠ k)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (h : ℝ → ℝ)
    (hm : MonotoneOn (fun t => σ*γ t i) (Icc a b))
    (he : ∀ t ∈ Icc a b, h (σ*γ t i) = γ t k)
    (ho : ∀ q ∈ Icc (σ*γ a i) (σ*γ b i), ∃ t ∈ Icc a b, σ*γ t i=q) :
    signedPlanarCenterlineGraph γ a b i σ h =
      {x : Fin 2 → ℝ | ∃ t : ℝ, Sum.elim x (fun _ => t) ∈
        signedPlanarRestrictedPath γ a b i σ} := by
  ext x
  change (x 0 ∈ Icc (σ*γ a i) (σ*γ b i) ∧ x 1 = h (x 0)) ↔ _
  constructor
  · rintro ⟨hq, hz⟩
    obtain ⟨t, ht, hq'⟩ := ho (x 0) hq
    refine ⟨t, ?_⟩
    change (t ∈ Icc (0 : ℝ) 1 ∧ signedPlanarDecode i σ x = γ t) ∧ t ∈ Icc a b
    refine ⟨⟨⟨ha.trans ht.1, ht.2.trans hb⟩, ?_⟩, ht⟩
    apply (signedPlanarDecode_eq_iff i k hik σ hσ x (γ t)).mpr
    exact ⟨hq'.symm, hz.trans (by rw [← hq']; exact he t ht)⟩
  · rintro ⟨t, ht⟩
    change (t ∈ Icc (0 : ℝ) 1 ∧ signedPlanarDecode i σ x = γ t) ∧ t ∈ Icc a b at ht
    obtain ⟨hq, hz⟩ := (signedPlanarDecode_eq_iff i k hik σ hσ x (γ t)).mp ht.1.2
    refine ⟨?_, ?_⟩
    · rw [hq]
      exact ⟨hm ⟨le_rfl, hab⟩ ht.2 ht.2.1, hm ht.2 ⟨hab, le_rfl⟩ ht.2.2⟩
    · rw [hq, he t ht.2]
      exact hz

theorem published_signedPlanarCenterline_uniform_format
    (hQQE : PublishedQuantitativeRealQE) (s D : ℕ) :
    ∃ sOut DOut : ℕ,
    ∀ (γ : ℝ → Fin 2 → ℝ) (A : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ)),
    A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) →
    PolynomialSignDetermined A (unitPathGraph γ) →
    ∀ (a b : ℝ), a ≤ b → 0 ≤ a → b ≤ 1 →
    ∀ (i k : Fin 2), i ≠ k → ∀ σ : ℝ, (σ=1 ∨ σ= -1) → ∀ h : ℝ → ℝ,
    MonotoneOn (fun t => σ*γ t i) (Icc a b) →
    (∀ t ∈ Icc a b, h (σ*γ t i) = γ t k) →
    (∀ q ∈ Icc (σ*γ a i) (σ*γ b i), ∃ t ∈ Icc a b, σ*γ t i=q) →
    ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
      (∀ p ∈ B, p.totalDegree ≤ DOut) ∧
      PolynomialSignDetermined B (signedPlanarCenterlineGraph γ a b i σ h) := by
  obtain ⟨sOut, DOut, hQ⟩ := published_bounded_time_projection_format hQQE (Fin 2) (s+2) (max D 1)
  refine ⟨sOut, DOut, ?_⟩
  intro γ A hc hd hG a b hab ha hb i k hik σ hσ h hm he ho
  obtain ⟨B, hBc, hBd, hBG⟩ := signedPlanarRestrictedPath_bounded_format γ A s D hc hd hG a b i σ
  rw [signedPlanarCenterlineGraph_eq_projection γ a b hab ha hb i k hik σ hσ h hm he ho]
  exact hQ B _ hBc hBd hBG

end PaperI
