import PaperILean.FixedDRelativeStage
import PaperILean.FixedDFiberComponents
import PaperILean.ExceptionalDSections
import PaperILean.ComponentHardtSections
import PaperILean.ExceptionalPackingBounds

/-! I3244[218,275): counting original indexed labels over the actual finite
exceptional d-list. The family-packing hypothesis is the source hypothesis at
I1338. Repeated representatives retain their distinct labels. -/
noncomputable section
open scoped BigOperators
open scoped Matrix.L2OpNorm
namespace PaperI.ExceptionalFiberPackingStage
open Set Classical Matrix RegularSectionDifferential RegularSectionRates

/-- Count labels, not the image of their representatives, by actual components.
Packing is only used at an anchor which is itself an original label. -/
theorem indexed_component_card_bound {X ι : Type*} [TopologicalSpace X]
    (J : Finset ι) (g : ι → X) (S : Set X)
    [Finite (ConnectedComponents S)] (hg : ∀ i ∈ J, g i ∈ S)
    (B : ℝ) (hB : 0 ≤ B)
    (hlocal : ∀ i ∈ J,
      ((J.filter (fun j => g j ∈ connectedComponentIn S (g i))).card : ℝ) ≤ B) :
    (J.card : ℝ) ≤ (Nat.card (ConnectedComponents S) : ℝ) * B := by
  classical
  by_cases he : J = ∅
  · subst J
    simpa using mul_nonneg (Nat.cast_nonneg (α := ℝ) _) hB
  obtain ⟨i0,hi0⟩ := Finset.nonempty_iff_ne_empty.mpr he
  let lift : ι → S := fun i => if h : g i ∈ S then ⟨g i,h⟩ else ⟨g i0,hg i0 hi0⟩
  have hlift (i : ι) (hi : i ∈ J) : (lift i).val = g i := by simp [lift,hg i hi]
  let c : ι → ConnectedComponents S := fun i => ConnectedComponents.mk (lift i)
  letI : Fintype (ConnectedComponents S) := Fintype.ofFinite _
  have hsum : J.card = ∑ q : ConnectedComponents S, (J.filter (fun i => c i = q)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hb (q : ConnectedComponents S) :
      ((J.filter (fun i => c i = q)).card : ℝ) ≤ B := by
    by_cases hn : (J.filter (fun i => c i = q)).Nonempty
    · obtain ⟨i,hi⟩ := hn
      obtain ⟨hiJ,hiq⟩ := Finset.mem_filter.mp hi
      apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hlocal i hiJ)
      intro j hj
      obtain ⟨hjJ,hjq⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨hjJ,?_⟩
      have hcc : ConnectedComponents.mk (lift j) = ConnectedComponents.mk (lift i) :=
        hjq.trans hiq.symm
      have hm := (subtype_mem_connectedComponentIn_iff (lift i) (lift j)).mpr hcc
      simpa only [hlift i hiJ,hlift j hjJ] using hm
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
      simpa only [hempty,Finset.card_empty,Nat.cast_zero] using hB
  calc
    (J.card : ℝ) = ∑ q : ConnectedComponents S,
        ((J.filter (fun i => c i = q)).card : ℝ) := by rw [hsum]; norm_cast
    _ ≤ ∑ _q : ConnectedComponents S, B := Finset.sum_le_sum (fun q _ => hb q)
    _ = (Nat.card (ConnectedComponents S) : ℝ) * B := by simp [Nat.card_eq_fintype_card]

/-- Exact finite level decomposition retains all label multiplicities. -/
theorem indexed_levels_card_bound {ι : Type*} (J : Finset ι) (d : ι → ℝ)
    (C : Finset ℝ) (hd : ∀ i ∈ J, d i ∈ C) (B : ℝ)
    (hlevel : ∀ t ∈ C, ((J.filter (fun i => d i = t)).card : ℝ) ≤ B) :
    (J.card : ℝ) ≤ (C.card : ℝ) * B := by
  classical
  have hs : J.card = ∑ t ∈ C, (J.filter (fun i => d i = t)).card :=
    Finset.card_eq_sum_card_fiberwise hd
  calc
    (J.card : ℝ) = ∑ t ∈ C, ((J.filter (fun i => d i = t)).card : ℝ) := by rw [hs]; norm_cast
    _ ≤ ∑ _t ∈ C, B := Finset.sum_le_sum hlevel
    _ = (C.card : ℝ) * B := by simp

/-- The literal source radius, in the original fixed triangular representatives. -/
def relativeNeighborhoodRadius (a b : Fin 6 → ℝ) : ℝ :=
  max ‖(originalUpperLinearMatrix a)⁻¹ * originalUpperLinearMatrix b‖
    (max ‖((originalUpperLinearMatrix a)⁻¹ * originalUpperLinearMatrix b)⁻¹‖
      (physicalEuclideanNorm ((originalUpperLinearMatrix a)⁻¹ *ᵥ
        ((![b 2,b 4,b 5] : Fin 3 → ℝ) - ![a 2,a 4,a 5]))))

private theorem nat_le_power (P : ℝ) (hP : 2 ≤ P) (n : ℕ) :
    (n : ℝ) ≤ P^(n : ℝ) := by
  have hp : 0 < P := by linarith
  have h : (n : ℝ)+1 ≤ P^(n : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ,Real.rpow_add hp,Real.rpow_one]
      have hm := mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg hp.le (n : ℝ))
      have hn := Nat.cast_nonneg (α := ℝ) n
      nlinarith
  linarith

/-- Uniform exceptional-level packing for any bounded finite list. The indexed
local-packing premise is inherited from I1338 and is applied only at labels.
The component and relative-path bounds are derived, not premises. -/
theorem exceptional_levels_card_bound
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) (hk : 2 ≤ k) :
    ∃ N M : ℕ, ∀ (P Cs Cw Λ q : ℝ) (S0 : AugmentedState k)
      (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ))
      (C : Finset ℝ) (K : ℕ),
      2 ≤ P → 0 ≤ Λ → 0 ≤ q → A.card ≤ s →
      (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A E → C.card ≤ K →
      (∀ g ∈ E, augmentedStateNorm (augmentedPullback S0 g) ≤ P^Cw) →
      (∀ g ∈ E, P^(-Cs) ≤ descendingSingularValues
        (dComplement (augmentedPullback S0 g)) (Fin.last 4)) →
      ∀ {ι : Type} (J : Finset ι) (g : ι → Fin 6 → ℝ),
      (∀ i ∈ J, g i ∈ E) → (∀ i ∈ J, g i 3 ∈ C) →
      (∀ i ∈ J, ∀ R : ℝ, 2 ≤ R →
        ((J.filter (fun j => relativeNeighborhoodRadius (g i) (g j) ≤ R)).card : ℝ) ≤
          Λ * R^q) →
      (J.card : ℝ) ≤ Λ * P^((K*N : ℕ)+q*((M : ℝ)*
        (6*(Fintype.card (AugmentedCoordinateIndex k) : ℝ)+3*max Cs 0+3*max Cw 0+4)+5)) := by
  classical
  obtain ⟨N,hN⟩ := FixedDFiberComponents.actual_d_fiber_component_count_stage
    hCell.toFiniteConnectedCover hHardt.toHardtTriviality hQE s D
  obtain ⟨M,hM⟩ := FixedDRelativeStage.actual_fixed_d_relative_stage
    hCell hPath hHardt hQE hNash hPiece k (s+1) (max D 1) hk
  refine ⟨N,M,?_⟩
  intro P Cs Cw Λ q S0 A E C K hP hΛ _hq hAc hAd hAE hC hwindow hpivot ι J g hg hd hpack
  let e : ℝ := (M : ℝ)*(6*(Fintype.card (AugmentedCoordinateIndex k) : ℝ)+
    3*max Cs 0+3*max Cw 0+4)+5
  have he : 1 ≤ e := by
    have hh : 0 ≤ (M : ℝ)*(6*(Fintype.card (AugmentedCoordinateIndex k) : ℝ)+
        3*max Cs 0+3*max Cw 0+4) := by positivity
    dsimp [e]
    linarith
  have hpos : 0 < P := by linarith
  have hR : 2 ≤ P^e := hP.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ P) he)
  have hB : 0 ≤ Λ*(P^e)^q := mul_nonneg hΛ (Real.rpow_nonneg (by positivity) _)
  have hlevel (t : ℝ) :
      ((J.filter (fun i => g i 3 = t)).card : ℝ) ≤ (N : ℝ)*(Λ*(P^e)^q) := by
    let Et : Set (Fin 6 → ℝ) := {x | x ∈ E ∧ x 3 = t}
    let Jt := J.filter (fun i => g i 3 = t)
    have hcount := hN A E hAc hAd hAE t
    letI : Finite (ConnectedComponents Et) := hcount.1
    obtain ⟨At,hAtc,hAtd,hAtE⟩ := FixedDFiberComponents.actual_d_fiber_sign_format
      A E s D hAc hAd hAE t
    have hgt (i : ι) (hi : i ∈ Jt) : g i ∈ Et := by
      obtain ⟨hiJ,hit⟩ := Finset.mem_filter.mp hi
      exact ⟨hg i hiJ,hit⟩
    have hc : (Jt.card : ℝ) ≤ (Nat.card (ConnectedComponents Et) : ℝ)*(Λ*(P^e)^q) := by
      apply indexed_component_card_bound Jt g Et hgt _ hB
      intro i hi
      have hiJ : i ∈ J := (Finset.mem_filter.mp hi).1
      apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hpack i hiJ (P^e) hR)
      intro j hj
      obtain ⟨hjJt,hjcomp⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hjJt).1,?_⟩
      have hrel := hM P Cs Cw S0 At Et t hP hAtc hAtd hAtE
        (fun x hx => hx.2) (fun x hx => hwindow x hx.1) (fun x hx => hpivot x hx.1)
        (g i) (g i) (g j) (mem_connectedComponentIn (hgt i hi)) hjcomp
      exact ExceptionalPackingBounds.literal_relative_neighborhood_le (g i) (g j) (P^e) hrel.2
    exact hc.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount.2) hB)
  have hall := indexed_levels_card_bound J (fun i => g i 3) C hd
    ((N : ℝ)*(Λ*(P^e)^q)) (fun t _ => hlevel t)
  calc
    (J.card : ℝ) ≤ (C.card : ℝ)*((N : ℝ)*(Λ*(P^e)^q)) := hall
    _ ≤ (K : ℝ)*((N : ℝ)*(Λ*(P^e)^q)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hC) (mul_nonneg (Nat.cast_nonneg _) hB)
    _ = (K*N : ℕ)*(Λ*(P^e)^q) := by push_cast; ring
    _ ≤ P^((K*N : ℕ) : ℝ)*(Λ*(P^e)^q) :=
      mul_le_mul_of_nonneg_right (nat_le_power P hP (K*N)) hB
    _ = Λ * P^((K*N : ℕ)+q*((M : ℝ)*
        (6*(Fintype.card (AugmentedCoordinateIndex k) : ℝ)+3*max Cs 0+3*max Cw 0+4)+5)) := by
      rw [← Real.rpow_mul hpos.le, ← mul_assoc, mul_comm _ Λ, mul_assoc,
        ← Real.rpow_add hpos]
      congr 2
      dsimp [e]
      ring

open ActualDSections ExceptionalDSections

/-- Complete exceptional-fiber label-count application to the actual constructed
finite list. All saved whole-axis, section, format and fixed-order assignment
certificates are retained. The cut list is not an arbitrary empty witness. -/
theorem actual_exceptional_fiber_packing_stage
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) (hk : 2 ≤ k) :
    ∃ nAtlas sOut dOut K N M : ℕ,
      ∀ (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A E →
      ∃ (F : ComponentSectionAtlas (actualDRelation E)) (C : Finset ℝ),
        F.Bounded nAtlas sOut dOut ∧ Nonempty (FixedOrderAssignment F sOut dOut) ∧
        C.card ≤ K ∧ C.powerset.card ≤ 2^K ∧
        (∀ t : ℝ, t ∈ C ∨ ∃ L ∈ C.powerset, t ∈ axisCutCell C L) ∧
        (∀ L ∈ C.powerset, ∀ M ∈ C.powerset, L ≠ M →
          Disjoint (axisCutCell C L) (axisCutCell C M)) ∧
        (∀ L ∈ C.powerset, IsOpen (axisCutCell C L) ∧
          IsPreconnected (axisCutCell C L) ∧
          (∀ t ∈ axisCutCell C L, t ∉ C) ∧
          ((∀ t ∈ axisCutCell C L,
              projectionFiber (actualDRelation E) (fun _ => t) = ∅) ∨
            ∃ (i : Fin F.n) (hU : parameterCell C L ⊆ F.piece i),
              (∀ j : Fin (F.m i),
                Continuous (restrictSection F i j C L hU) ∧
                HasBoundedSignFormat (sOut+K) (max dOut 1)
                  (componentSectionGraph (parameterCell C L) (restrictSection F i j C L hU)) ∧
                HasBoundedSignFormat (sOut+K) (max dOut 1)
                  (componentSectionRegion (actualDRelation E) (parameterCell C L)
                    (restrictSection F i j C L hU))) ∧
              (∀ j (p : parameterCell C L),
                restrictSection F i j C L hU p ∈ E ∧
                (restrictSection F i j C L hU p) 3 = p.val 0) ∧
              ∀ p : parameterCell C L, Function.Bijective
                (fun j => ConnectedComponents.mk
                  (⟨restrictSection F i j C L hU p,
                    F.section_mem i j ⟨p.val,hU p.property⟩⟩ :
                    projectionFiber (actualDRelation E) p.val)))) ∧
        (∀ (P Cs Cw Λ q : ℝ) (S0 : AugmentedState k),
          2 ≤ P → 0 ≤ Λ → 0 ≤ q →
          (∀ g ∈ E, augmentedStateNorm (augmentedPullback S0 g) ≤ P^Cw) →
          (∀ g ∈ E, P^(-Cs) ≤ descendingSingularValues
            (dComplement (augmentedPullback S0 g)) (Fin.last 4)) →
          ∀ {ι : Type} (J : Finset ι) (g : ι → Fin 6 → ℝ),
          (∀ i ∈ J, g i ∈ E) → (∀ i ∈ J, g i 3 ∈ C) →
          (∀ i ∈ J, ∀ R : ℝ, 2 ≤ R →
            ((J.filter (fun j => relativeNeighborhoodRadius (g i) (g j) ≤ R)).card : ℝ) ≤
              Λ * R^q) →
          (J.card : ℝ) ≤ Λ * P^((K*N : ℕ)+q*((M : ℝ)*
            (6*(Fintype.card (AugmentedCoordinateIndex k) : ℝ)+
              3*max Cs 0+3*max Cw 0+4)+5))) := by
  classical
  obtain ⟨nAtlas,sOut,dOut,K,hCuts⟩ := ExceptionalDSections.actual_d_exceptional_list
    hCell hHardt hQE s D
  obtain ⟨N,M,hCount⟩ := exceptional_levels_card_bound
    hCell hPath hHardt hQE hNash hPiece k s D hk
  refine ⟨nAtlas,sOut,dOut,K,N,M,?_⟩
  intro A E hAc hAd hAE
  obtain ⟨F,C,hF,hAssign,hC,hPowers,hCover,hDisjoint,hCells⟩ := hCuts A E hAc hAd hAE
  refine ⟨F,C,hF,hAssign,hC,hPowers,hCover,hDisjoint,hCells,?_⟩
  intro P Cs Cw Λ q S0 hP hΛ hq hWindow hPivot ι J g hg hd hPacking
  exact hCount P Cs Cw Λ q S0 A E C K hP hΛ hq hAc hAd hAE hC
    hWindow hPivot J g hg hd hPacking

end PaperI.ExceptionalFiberPackingStage
