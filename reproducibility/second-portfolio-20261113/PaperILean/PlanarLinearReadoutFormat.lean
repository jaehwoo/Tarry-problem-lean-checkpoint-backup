import PaperILean.CoordinatePathFormat

/-! Fixed linear readouts x,y,x+y,x-y for I1263. Their graph format is
derived from the actual domain description; no function-format oracle is used.
Range bounds use the Euclidean diameter, not the default coordinate sup norm. -/

noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def planarReadoutPolynomial (i : Fin 4) : MvPolynomial (Fin 2) ℝ :=
  if i=0 then MvPolynomial.X 0 else if i=1 then MvPolynomial.X 1 else
    if i=2 then MvPolynomial.X 0+MvPolynomial.X 1 else MvPolynomial.X 0-MvPolynomial.X 1

def planarReadout (i : Fin 4) (x : Fin 2 → ℝ) : ℝ :=
  MvPolynomial.eval x (planarReadoutPolynomial i)

theorem planarReadoutPolynomial_degree (i : Fin 4) :
    (planarReadoutPolynomial i).totalDegree ≤ 1 := by
  fin_cases i <;> simp only [planarReadoutPolynomial,Fin.isValue,↓reduceIte]
  · simp
  · simp
  · exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)

theorem planarReadout_continuous (i : Fin 4) : Continuous (planarReadout i) := by
  unfold planarReadout
  fin_cases i
  · simpa [planarReadoutPolynomial] using (continuous_apply (0 : Fin 2) : Continuous (fun x : Fin 2 → ℝ => x 0))
  · simpa [planarReadoutPolynomial] using (continuous_apply (1 : Fin 2) : Continuous (fun x : Fin 2 → ℝ => x 1))
  · simpa [planarReadoutPolynomial] using
      ((continuous_apply (0 : Fin 2)).add (continuous_apply (1 : Fin 2)) : Continuous (fun x : Fin 2 → ℝ => x 0+x 1))
  · simpa [planarReadoutPolynomial] using
      ((continuous_apply (0 : Fin 2)).sub (continuous_apply (1 : Fin 2)) : Continuous (fun x : Fin 2 → ℝ => x 0-x 1))

def planarReadoutGraphPolynomial (i : Fin 4) : MvPolynomial (Fin 2 ⊕ Unit) ℝ :=
  MvPolynomial.X (Sum.inr ())-MvPolynomial.rename Sum.inl (planarReadoutPolynomial i)

theorem planarReadoutGraphPolynomial_degree (i : Fin 4) :
    (planarReadoutGraphPolynomial i).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp
  · exact (MvPolynomial.totalDegree_rename_le _ _).trans (planarReadoutPolynomial_degree i)

theorem planarReadout_graph_sign_description
    (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ))
    (hS : PolynomialSignDetermined A S) (i : Fin 4) :
    PolynomialSignDetermined
      (A.image (MvPolynomial.rename Sum.inl) ∪ {planarReadoutGraphPolynomial i})
      (scalarFunctionGraph S (planarReadout i)) := by
  intro x y hxy
  have hDom : (fun k => x (Sum.inl k)) ∈ S ↔ (fun k => y (Sum.inl k)) ∈ S := by
    apply hS
    intro q hq
    simpa only [MvPolynomial.eval_rename,Function.comp_def] using
      hxy (MvPolynomial.rename Sum.inl q)
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩))
  have he := (hxy (planarReadoutGraphPolynomial i)
    (Finset.mem_union_right _ (Finset.mem_singleton_self _))).1
  simp only [planarReadoutGraphPolynomial,map_sub,MvPolynomial.eval_X,MvPolynomial.eval_rename,
    Function.comp_def,sub_eq_zero] at he
  exact and_congr hDom he

theorem planarReadout_graph_bounded_sign_format
    (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)) (s D : ℕ)
    (hcard : A.card ≤ s) (hdegree : ∀ q ∈ A, q.totalDegree ≤ D)
    (hS : PolynomialSignDetermined A S) (i : Fin 4) :
    ∃ B : Finset (MvPolynomial (Fin 2 ⊕ Unit) ℝ), B.card ≤ s+1 ∧
      (∀ q ∈ B, q.totalDegree ≤ max D 1) ∧
      PolynomialSignDetermined B (scalarFunctionGraph S (planarReadout i)) := by
  classical
  refine ⟨A.image (MvPolynomial.rename Sum.inl) ∪ {planarReadoutGraphPolynomial i},?_,?_,
    planarReadout_graph_sign_description A S hS i⟩
  · calc
      _ ≤ (A.image (MvPolynomial.rename Sum.inl)).card +
          ({planarReadoutGraphPolynomial i} : Finset _).card := Finset.card_union_le _ _
      _ ≤ s+1 := by simpa only [Finset.card_singleton] using
        Nat.add_le_add_right (Finset.card_image_le.trans hcard) 1
  · intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
      exact (MvPolynomial.totalDegree_rename_le _ _).trans ((hdegree p hp).trans (Nat.le_max_left _ _))
    · rw [Finset.mem_singleton.mp hq]
      exact (planarReadoutGraphPolynomial_degree i).trans (Nat.le_max_right _ _)

theorem planarReadout_range_le_two_diameter
    (S : Set (Fin 2 → ℝ))
    (hS : Bornology.IsBounded ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' S))
    (i : Fin 4) (x : Fin 2 → ℝ) (hx : x ∈ S) (y : Fin 2 → ℝ) (hy : y ∈ S) :
    |planarReadout i x-planarReadout i y| ≤
      2*Metric.diam ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' S) := by
  have h0 := coordinate_range_le_euclidean_diameter S hS 0 x hx y hy
  have h1 := coordinate_range_le_euclidean_diameter S hS 1 x hx y hy
  have hn := Metric.diam_nonneg (s := (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' S)
  fin_cases i <;> simp [planarReadout,planarReadoutPolynomial]
  · linarith
  · linarith
  · have he : x 0+x 1-(y 0+y 1)=(x 0-y 0)+(x 1-y 1) := by ring
    rw [he]
    exact (abs_add _ _).trans (by linarith)
  · have he : x 0-x 1-(y 0-y 1)=(x 0-y 0)-(x 1-y 1) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)

end PaperI
