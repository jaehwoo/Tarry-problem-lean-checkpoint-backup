import PaperILean.GoodStripJointFamily

noncomputable section

namespace PaperI.GoodStrips

open Set FirstOrder MeasureTheory
open scoped ENNReal

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private abbrev RD {α : Type} (S : Set (α → ℝ)) :=
  (univ : Set ℝ).Definable Language.ring S

abbrev GoodStripParameters (ι : Type) (sA dA sG dG : ℕ) :=
  ((ScalarParameters (Fin 2) sA dA ⊕
    (ι × ScalarParameters (Fin 3) sG dG)) ⊕ Fin 4)

abbrev GoodStripTables (ι : Type) (sA sG : ℕ) := SignTable sA × (ι → SignTable sG)

private def AFamily {ι : Type} (sA dA sG dG : ℕ)
    (b : GoodStripTables ι sA sG) :
    Set (GoodStripParameters ι sA dA sG dG ⊕ Fin 2 → ℝ) :=
  parameterPlaneLift (Sum.inl ∘ Sum.inl) (universalPolynomialBooleanSet (Fin 2) sA dA b.1)

private def GFamily {ι : Type} (sA dA sG dG : ℕ)
    (b : GoodStripTables ι sA sG) (i : ι) :
    Set (GoodStripParameters ι sA dA sG dG ⊕ Fin 3 → ℝ) :=
  parameterGraphLift (Sum.inl ∘ Sum.inr ∘ Prod.mk i)
    (universalPolynomialBooleanSet (Fin 3) sG dG (b.2 i))

/-- Fixed input sign bounds precede the actual graphs, coefficients, rectangle,
amplitudes, subset density and chosen loss fraction. -/
theorem derivative_good_points_fixed_format
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedPiecewiseNashExtensions)
    {ι : Type} [Fintype ι] (sA dA sG dG N : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧
    ∀ (S : Set (Fin 2 → ℝ)) (F : Finset (MvPolynomial (Fin 2) ℝ)),
      F.card ≤ sA → (∀ q ∈ F, q.totalDegree ≤ dA) → PolynomialSignDetermined F S →
    ∀ (G : ι → Set (Fin 3 → ℝ)) (J : ι → Finset (MvPolynomial (Fin 3) ℝ)),
      (∀ i, (J i).card ≤ sG) → (∀ i q, q ∈ J i → q.totalDegree ≤ dG) →
      (∀ i, PolynomialSignDetermined (J i) (G i)) →
    ∀ (f : ι → ℝ × ℝ → ℝ) (M : ι → ℝ) (x0 x1 y0 y1 : ℝ),
      let R := Rect x0 x1 y0 y1
      let L := x1-x0
      let W := y1-y0
      let A := {z : ℝ × ℝ | ![z.1,z.2] ∈ S} ∩ R
      x0 < x1 → y0 < y1 →
      (∀ i z, z ∈ R → ∀ w, ![z.1,z.2,w] ∈ G i ↔ w = f i z) →
      (∀ i, 0 ≤ M i) →
      (∀ i z, z ∈ A → |f i z| ≤ M i) →
      ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∃ U : Set (ℝ × ℝ), MeasurableSet U ∧ U ⊆ A ∧
        volume (A \ U) ≤ ENNReal.ofReal (η*L*W) ∧
        ∀ z ∈ U, ∀ i a b, a+b ≤ N →
          |Jet (f i) a b z| ≤ D*(1/η)^(4*N)*M i/(L^a*W^b) := by
  classical
  let Γ := GoodStripParameters ι sA dA sG dG
  let Θ := GoodStripTables ι sA sG
  let e : Fin 4 → Γ := Sum.inr
  have hA (b : Θ) : RD (AFamily sA dA sG dG b) :=
    parameterPlaneLift_definable _ (hasPolynomialSignDescription_definable
      (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) sA dA b.1))
  have hG (b : Θ) (i : ι) : RD (GFamily sA dA sG dG b i) :=
    parameterGraphLift_definable _ (hasPolynomialSignDescription_definable
      (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 3) sG dG (b.2 i)))
  have hh (b : Θ) := preparation_joint_family hDD hCell hHardt hQE hNash
    (AFamily sA dA sG dG b) (GFamily sA dA sG dG b) (hA b) (hG b)
    (e 0) (e 1) (e 2) (e 3) N
  choose K hK hprep using hh
  let D := 1 + ∑ b : Θ, K b
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun b _ => zero_le_one.trans (hK b))
  refine ⟨D,hD,?_⟩
  intro S F hFc hFd hFS G J hJc hJd hJG f M x0 x1 y0 y1
  dsimp only
  intro hx hy hf hM hAmp η hη hη1
  obtain ⟨bA,pA,hRepA⟩ := signFormat_universal sA dA S F hFc hFd hFS
  choose bG pG hRepG using fun i => signFormat_universal sG dG (G i) (J i)
    (hJc i) (hJd i) (hJG i)
  let b : Θ := (bA,bG)
  let p : Γ → ℝ := Sum.elim (Sum.elim pA (fun j => pG j.1 j.2)) ![x0,x1,y0,y1]
  have hp (j : Fin 4) : p (e j) = (![x0,x1,y0,y1] : Fin 4 → ℝ) j := rfl
  have he : planeFiber (AFamily sA dA sG dG b) p =
      {z : ℝ × ℝ | ![z.1,z.2] ∈ S} := by
    rw [AFamily,parameterPlaneLift_fiber]
    ext z
    exact hRepA _
  have hGraph (i : ι) : RealizesOn (GFamily sA dA sG dG b i) p (f i)
      (Rect (p (e 0)) (p (e 1)) (p (e 2)) (p (e 3))) := by
    intro z hz y
    have hrect : z ∈ Rect x0 x1 y0 y1 := by simpa only [hp] using hz
    rw [GFamily,parameterGraphLift_value]
    exact (hRepG i _).trans (hf i z hrect y)
  have hAmp' : ∀ i z, z ∈ planeFiber (AFamily sA dA sG dG b) p ∩
      Rect (p (e 0)) (p (e 1)) (p (e 2)) (p (e 3)) → |f i z| ≤ M i := by
    intro i z hz
    apply hAmp i z
    simpa only [he,hp] using hz
  obtain ⟨U,hUm,hUsub,hUV,hDeriv⟩ := hprep b p f M
    (by simpa only [hp] using hx) (by simpa only [hp] using hy)
    hGraph hM hAmp' η hη hη1
  refine ⟨U,hUm,by simpa only [he,hp] using hUsub,by simpa only [he,hp] using hUV,?_⟩
  intro z hz i a c hac
  have hkD : K b ≤ D := by
    apply (Finset.single_le_sum (fun j _ => zero_le_one.trans (hK j)) (Finset.mem_univ b)).trans
    exact le_add_of_nonneg_left zero_le_one
  apply (show |Jet (f i) a c z| ≤ K b*(1/η)^(4*N)*M i/((x1-x0)^a*(y1-y0)^c) from
    by simpa only [hp] using hDeriv z hz i a c hac).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkD (by positivity)) (hM i))
    (mul_nonneg (pow_nonneg (sub_nonneg.mpr hx.le) _) (pow_nonneg (sub_nonneg.mpr hy.le) _))

end PaperI.GoodStrips
