import PaperILean.GoodStripThresholdSets
import PaperILean.GoodStripSmoothSections
import PaperILean.PreparationFormat
import PaperILean.PublishedUniformComponents

noncomputable section

namespace PaperI.GoodStrips

open Set FirstOrder MeasureTheory
open scoped ENNReal ContDiff

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private abbrev RD {α : Type} (S : Set (α → ℝ)) :=
  (univ : Set ℝ).Definable Language.ring S

private theorem scalar_section_bound {α : Type} [Finite α]
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (A : Set (α ⊕ Fin 2 → ℝ)) (hA : RD A) (axis : Bool) :
    ∃ K : ℕ, ∀ (p : α → ℝ) (u : ℝ),
      Preparation.ComponentBound K (Preparation.sectionPoint axis u ⁻¹' planeFiber A p) := by
  let E := sectionFamily axis A
  obtain ⟨K,hK⟩ := published_finite_family_projection_fiber_component_bound
    hCell hHardt hQE (fun _ : Unit => E)
    (fun _ => hQE.finite_sign_description E (sectionFamily_definable axis hA))
  refine ⟨K,fun p u => ?_⟩
  have hb := finite_connectedComponents_and_card_le_of_homeomorph
    (projectionFiberUnitHomeomorphScalar E (Sum.elim p (fun _ : Unit => u)))
    (hK () (Sum.elim p (fun _ : Unit => u)))
  rwa [sectionFamily_fiber axis A p u] at hb

/-- For a fixed actual semialgebraic input family, one threshold constant works
for all fibers, amplitudes, positive rectangle widths and loss fractions. -/
theorem preparation_joint_family
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedPiecewiseNashExtensions)
    {α ι : Type} [Finite α] [Fintype ι]
    (A : Set (α ⊕ Fin 2 → ℝ)) (G : ι → Set (α ⊕ Fin 3 → ℝ))
    (hA : RD A) (hG : ∀ i, RD (G i))
    (x0 x1 y0 y1 : α) (N : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧
    ∀ (p : α → ℝ) (f : ι → ℝ × ℝ → ℝ) (M : ι → ℝ),
      let R := Rect (p x0) (p x1) (p y0) (p y1)
      let L := p x1-p x0
      let W := p y1-p y0
      p x0 < p x1 → p y0 < p y1 →
      (∀ i, RealizesOn (G i) p (f i) R) →
      (∀ i, 0 ≤ M i) →
      (∀ i z, z ∈ planeFiber A p ∩ R → |f i z| ≤ M i) →
      ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∃ S : Set (ℝ × ℝ), MeasurableSet S ∧ S ⊆ planeFiber A p ∩ R ∧
        volume ((planeFiber A p ∩ R) \ S) ≤ ENNReal.ofReal (η*L*W) ∧
        ∀ z ∈ S, ∀ i a b, a+b ≤ N →
          |Jet (f i) a b z| ≤ D*(1/η)^(4*N)*M i/(L^a*W^b) := by
  classical
  let B := boxFamily x0 x1 y0 y1
  let A₀ := A ∩ B
  have hB : RD B := boxFamily_definable x0 x1 y0 y1
  have hA₀ : RD A₀ := hA.inter hB
  let U := regularPlane G A₀ N
  have hU : RD U := regularPlane_definable G hG hA₀ N
  let V := hGoodFamily U G N
  have hV : RD V := hGoodFamily_definable hU hG N
  obtain ⟨KU,hKU⟩ := scalar_section_bound hCell hHardt hQE U hU true
  obtain ⟨KV,hKV⟩ := scalar_section_bound hCell hHardt hQE V hV false
  let jets (j : ThresholdIndex ι N) := mixedJetGraph (G j.1) j.2.1.val j.2.2.val
  have hjets (j : ThresholdIndex ι N) : RD (jets j) :=
    mixedJetGraph_definable (hG j.1) j.2.1.val j.2.2.val
  obtain ⟨KD,hKD⟩ := Preparation.published_uniform_field_section_components hCell hHardt hQE jets hjets
  obtain ⟨D,hD,prep⟩ := quantitative_preparation_on_open_subsets hDD (ι := ι) N KU KD KV
  refine ⟨D,hD,?_⟩
  intro p f M
  dsimp only
  intro hx hy hf hM hamp η hη hη1
  let R := Rect (p x0) (p x1) (p y0) (p y1)
  let L := p x1-p x0
  let W := p y1-p y0
  let U₀ := planeFiber U p
  have hR : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hBf : planeFiber B p = R := boxFamily_fiber x0 x1 y0 y1 p
  have hA₀f : planeFiber A₀ p = planeFiber A p ∩ R := by
    rw [show A₀ = A ∩ B from rfl,planeFiber_inter,hBf]
  have hsub : planeFiber A₀ p ⊆ R := by rw [hA₀f]; exact inter_subset_right
  have hU₀ : U₀ ⊆ planeFiber A₀ p := regularPlane_fiber_subset G A₀ N p
  have hUR : U₀ ⊆ R := hU₀.trans hsub
  have ho : IsOpen U₀ := regularPlane_fiber_open G A₀ N p
  have hnull : volume (planeFiber A₀ p \ U₀) = 0 := by
    apply regularPlane_fiber_null hNash hQE G N hA₀ p f hR hsub hf
    intro i
    have hFi : RealizesOn (G i) p (f i) (planeFiber B p) := hBf.symm ▸ hf i
    simpa only [hBf] using scalarGraph_sign_of_realizesOn hQE hB (hG i) p (f i) hFi
  have hVf (C : ℝ) : planeFiber V (hGoodParameter (N := N) p M C L) =
      horizontalGoodOn U₀ f N M C L := hGoodFamily_fiber hR hUR hf M C L
  have hBmeas (C₀ C : ℝ) (a : ℕ) :
      MeasurableSet (verticalBadOn (horizontalGoodOn U₀ f N M C₀ L) f N a M C L W) := by
    let q := hGoodParameter (N := N) p M C₀ L
    have hq : q ∘ Sum.inl = p := rfl
    have hVR : planeFiber V q ⊆ R := by
      rw [hVf C₀]
      exact fun _ hz => hUR hz.1
    let GG (i : ι) := parameterGraphLift Sum.inl (G i) (α := ThresholdParam α ι N)
    have hGG (i : ι) : RD (GG i) := parameterGraphLift_definable Sum.inl (hG i)
    have hfG (i : ι) : RealizesOn (GG i) q (f i) R := by
      intro z hz y
      exact (parameterGraphLift_value Sum.inl (G i) q z y).trans (hf i z hz y)
    have hv := vBadFamily_fiber (N := N) (a := a) (V := V) (G := GG) hR hVR hfG M C L W
    rw [← hVf C₀, ← hv]
    exact planeFiber_measurable hQE (vBadFamily_definable hV hGG N a) _
  have hFx (i : ι) (y : ℝ) :
      ContDiffOn ℝ N (fun x => f i (x,y)) (horizontalSection U₀ y) :=
    regularPlane_horizontal_smooth G A₀ N p f hR hsub hf i y
  have hFy (i : ι) (a : ℕ) (ha : a ≤ N) (x : ℝ) :
      ContDiffOn ℝ ((N-a : ℕ) : WithTop ℕ∞) (fun y => Jet (f i) a 0 (x,y))
        (verticalSection U₀ x) :=
    regularPlane_vertical_smooth G A₀ N p f hR hsub hf i a ha x
  have hJ := (hKD p (fun j => Jet (f j.1) j.2.1.val j.2.2.val)
      (p x0) (p x1) (p y0) (p y1)
      (fun j => mixedJetGraph_realizesOn hR (hf j.1) j.2.1.val j.2.2.val)).1
  have hxcount : ∀ i n, 0 < n → n ≤ N → ∀ y l r T sign,
      Ioo l r ⊆ horizontalSection U₀ y →
      Preparation.ComponentBound KD (signedIteratedDerivativeSuperlevel (fun x => f i (x,y)) n l r T sign) := by
    intro i n _ hn y l r T sign hsect
    let j : ThresholdIndex ι N := (i,⟨n,by omega⟩,0)
    have hb := hJ j true y l r T sign (fun t ht => hUR (hsect ht))
    simpa only [j, Preparation.signedFieldSection, signedIteratedDerivativeSuperlevel,
      Preparation.sectionPoint, Bool.true_eq, if_true, Fin.val_zero,
      Preparation.mixedJet_zero_right, Preparation.horizontalJet_eq_iteratedDeriv] using hb
  have hycount : ∀ i a b, 0 < b → a+b ≤ N → ∀ x l r T sign,
      Ioo l r ⊆ verticalSection U₀ x →
      Preparation.ComponentBound KD (signedIteratedDerivativeSuperlevel
        (fun y => Jet (f i) a 0 (x,y)) b l r T sign) := by
    intro i a b _ hab x l r T sign hsect
    let j : ThresholdIndex ι N := (i,⟨a,by omega⟩,⟨b,by omega⟩)
    have hb := hJ j false x l r T sign (fun t ht => hUR (hsect ht))
    simpa only [j, Preparation.signedFieldSection, signedIteratedDerivativeSuperlevel,
      Preparation.sectionPoint, Bool.false_eq_true, if_false, Preparation.mixedJet_eq_iteratedDeriv] using hb
  obtain ⟨S,hSm,hSU,hSvol,hderiv⟩ := prep η hη hη1 f M (p x0) (p x1) (p y0) (p y1) U₀
    hx hy ho hUR hM (fun i z hz => hamp i z (hA₀f ▸ hU₀ hz))
    hFx hFy (hKU p) (fun C x => hVf C ▸ hKV _ x)
    (fun C => hVf C ▸ planeFiber_measurable hQE hV _)
    hBmeas hxcount hycount
  refine ⟨S,hSm,fun z hz => hA₀f ▸ hU₀ (hSU hz),?_,hderiv⟩
  have hc : (planeFiber A p ∩ R) \ S ⊆ (planeFiber A₀ p \ U₀) ∪ (U₀ \ S) := by
    intro z hz
    by_cases hu : z ∈ U₀
    · exact Or.inr ⟨hu,hz.2⟩
    · exact Or.inl ⟨hA₀f.symm ▸ hz.1,hu⟩
  exact (measure_mono hc).trans ((measure_union_le _ _).trans (by rw [hnull,zero_add]; exact hSvol))

end PaperI.GoodStrips
