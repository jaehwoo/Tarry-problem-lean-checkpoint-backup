import PaperILean.DerivativeSignSubdivision

/-! Refining actual analytic and derivative-sign cut sets. Every added cut is
counted. The finite-family union includes both endpoints even for an empty
family. No uniform scalar-subdivision theorem is assumed here.
Pre-strategy diagnostics: checkpoint_108_027_cut_refinement_obstructions.log. -/

noncomputable section
namespace PaperI
open Set
open scoped BigOperators

theorem derivativeSignOn_mono {f : ℝ → ℝ} {S T : Set ℝ}
    (h : DerivativeSignOn f S) (hTS : T ⊆ S) : DerivativeSignOn f T := by
  rcases h with hp | hn | hz
  · exact Or.inl (fun x hx => hp x (hTS hx))
  · exact Or.inr (Or.inl (fun x hx => hn x (hTS hx)))
  · exact Or.inr (Or.inr (fun x hx => hz x (hTS hx)))

/-- A hereditary open-interval property survives a genuine finite refinement. -/
theorem consecutive_cut_property_refinement
    (P : ℝ → ℝ → Prop)
    (hmono : ∀ l r u v, l ≤ u → v ≤ r → P l r → P u v)
    (C D : Finset ℝ) {a b : ℝ} (ha : a ∈ C) (hb : b ∈ C)
    (hD : ∀ c ∈ D, c ∈ Icc a b) (hsub : C ⊆ D)
    (hP : ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) → P u v) :
    ∀ u ∈ D, ∀ v ∈ D, u < v → (∀ c ∈ D, c ∉ Ioo u v) → P u v := by
  intro u hu v hv huv hgap
  obtain ⟨l,hl,r,hr,hlu,hvr,hlr,hnone⟩ :=
    exists_consecutive_cuts_containing C ha hb (hD u hu).1 (hD v hv).2 huv
      (fun c hc => hgap c (hsub hc))
  exact hmono l r u v hlu hvr (hP l hl r hr hlr hnone)

/-- Analytic cuts and sign cuts are united, with both cardinalities retained. -/
theorem analytic_sign_cuts_union
    (f : ℝ → ℝ) (A S : Finset ℝ) {a b : ℝ}
    (haA : a ∈ A) (hbA : b ∈ A) (haS : a ∈ S) (hbS : b ∈ S)
    (hA : ∀ c ∈ A, c ∈ Icc a b) (hS : ∀ c ∈ S, c ∈ Icc a b)
    (han : ∀ u ∈ A, ∀ v ∈ A, u < v → (∀ c ∈ A, c ∉ Ioo u v) →
      AnalyticOnNhd ℝ f (Ioo u v))
    (hsign : ∀ u ∈ S, ∀ v ∈ S, u < v → (∀ c ∈ S, c ∉ Ioo u v) →
      DerivativeSignOn f (Ioo u v)) :
    ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
      C.card ≤ A.card + S.card ∧
      ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
        AnalyticOnNhd ℝ f (Ioo u v) ∧ DerivativeSignOn f (Ioo u v) := by
  classical
  let C := A ∪ S
  have hC : ∀ c ∈ C, c ∈ Icc a b := by
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · exact hA c h
    · exact hS c h
  have hanC := consecutive_cut_property_refinement
    (fun u v => AnalyticOnNhd ℝ f (Ioo u v))
    (fun _ _ _ _ hlu hvr h => h.mono (Ioo_subset_Ioo hlu hvr))
    A C haA hbA hC (Finset.subset_union_left) han
  have hsC := consecutive_cut_property_refinement
    (fun u v => DerivativeSignOn f (Ioo u v))
    (fun _ _ _ _ hlu hvr h => derivativeSignOn_mono h (Ioo_subset_Ioo hlu hvr))
    S C haS hbS hC (Finset.subset_union_right) hsign
  exact ⟨C,Finset.mem_union_left S haA,Finset.mem_union_left S hbA,hC,
    Finset.card_union_le A S,fun u hu v hv huv hgap =>
      ⟨hanC u hu v hv huv hgap,hsC u hu v hv huv hgap⟩⟩

/-- A single bounded cut set retains analyticity and the actual sign choice
for every function, including when the index type is empty. -/
theorem common_analytic_sign_cut_set
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (cuts : ι → Finset ℝ)
    (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ i, a ∈ cuts i) (hb : ∀ i, b ∈ cuts i)
    (hcuts : ∀ i, ∀ c ∈ cuts i, c ∈ Icc a b)
    (hcard : ∀ i, (cuts i).card ≤ K i)
    (hprops : ∀ i, ∀ u ∈ cuts i, ∀ v ∈ cuts i, u < v →
      (∀ c ∈ cuts i, c ∉ Ioo u v) →
      AnalyticOnNhd ℝ (f i) (Ioo u v) ∧ DerivativeSignOn (f i) (Ioo u v)) :
    ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
      C.card ≤ 2 + ∑ i, K i ∧
      ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
        ∀ i, AnalyticOnNhd ℝ (f i) (Ioo u v) ∧ DerivativeSignOn (f i) (Ioo u v) := by
  classical
  let C : Finset ℝ := {a,b} ∪ Finset.univ.biUnion cuts
  have haC : a ∈ C := Finset.mem_union_left _ (by simp)
  have hbC : b ∈ C := Finset.mem_union_left _ (by simp)
  have hsub (i : ι) : cuts i ⊆ C := by
    intro c hc
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hc⟩)
  have hC : ∀ c ∈ C, c ∈ Icc a b := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact ⟨le_rfl,hab⟩
      · exact ⟨hab,le_rfl⟩
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hc
      exact hcuts i c hi
  have hcardC : C.card ≤ 2 + ∑ i, K i := by
    calc
      C.card ≤ ({a,b} : Finset ℝ).card + (Finset.univ.biUnion cuts).card :=
        Finset.card_union_le _ _
      _ ≤ 2 + ∑ i, (cuts i).card :=
        add_le_add Finset.card_le_two Finset.card_biUnion_le
      _ ≤ 2 + ∑ i, K i := Nat.add_le_add_left (Finset.sum_le_sum (fun i _ => hcard i)) 2
  refine ⟨C,haC,hbC,hC,hcardC,?_⟩
  intro u hu v hv huv hgap i
  apply consecutive_cut_property_refinement
    (fun l r => AnalyticOnNhd ℝ (f i) (Ioo l r) ∧ DerivativeSignOn (f i) (Ioo l r))
    (fun _ _ _ _ hlu hvr h =>
      ⟨h.1.mono (Ioo_subset_Ioo hlu hvr),derivativeSignOn_mono h.2 (Ioo_subset_Ioo hlu hvr)⟩)
    (cuts i) C (ha i) (hb i) hC (hsub i) (hprops i) u hu v hv huv hgap

end PaperI
