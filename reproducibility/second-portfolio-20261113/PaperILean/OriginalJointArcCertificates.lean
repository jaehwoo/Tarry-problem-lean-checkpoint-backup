import PaperILean.JointOriginalArcData
import PaperILean.JointOriginalPreparation

/-! I1263/I1265: retain the four joint scalar graph witnesses already produced
by the original CAD construction. The finite direction is a parameter of one
joint graph. No pointwise polynomial encoding is selected after substitution. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

structure OriginalJointArcSelectorFamily {α : Type*}
    (P : Set (α → ℝ)) (g : (α → ℝ) → ℝ → Fin 2 → ℝ) where
  selector : Fin 4 → ((α ⊕ Fin 3) → ℝ) → ℝ
  measurable_selector : ∀ c, Measurable (selector c)
  semialgebraic_graph : ∀ c,
    HasPolynomialSignDescription (selectedFunctionGraph univ
      (fun p (_ : Unit) => selector c p))
  correct : ∀ c, ∀ p∈P, ∀ a∈Icc (0:ℝ) 1, ∀ b∈Icc (0:ℝ) 1, a≤b →
    DirectedPlanarGraphArc (g p) a b (planarDirectionI c)
      (planarDirectionK c) (planarDirectionSign c) →
    LipschitzOnWith 1 (fun x => selector c (Sum.elim p ![a,b,x]))
      (Icc (planarDirectionSign c*g p a (planarDirectionI c))
        (planarDirectionSign c*g p b (planarDirectionI c))) ∧
    (∀ r∈Icc a b, selector c (Sum.elim p ![a,b,
      planarDirectionSign c*g p r (planarDirectionI c)])=g p r (planarDirectionK c)) ∧
    ∀ x∈Icc (planarDirectionSign c*g p a (planarDirectionI c))
      (planarDirectionSign c*g p b (planarDirectionI c)),
      ∃ r∈Icc a b, x=planarDirectionSign c*g p r (planarDirectionI c) ∧
        selector c (Sum.elim p ![a,b,x])=g p r (planarDirectionK c)

theorem published_original_joint_arc_selector_family
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity) (hHardt : PublishedSemialgebraicHardtTriviality)
    {α : Type} [Finite α] {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g)) :
    Nonempty (OriginalJointArcSelectorFamily P g) := by
  classical
  choose Fs hFm hFs hF using fun c : Fin 4 => published_joint_projected_arc_graph
    hCAD hQE hHardt hg (planarDirectionI c) (planarDirectionK c) (planarDirectionSign c)
  exact ⟨⟨Fs,hFm,hFs,hF⟩⟩

def jointOriginalArcScalarGraph {α : Type*}
    (Fs : Fin 4 → ((α ⊕ Fin 3) → ℝ) → ℝ) :
    Set (((α ⊕ Fin 3) ⊕ Fin 2) → ℝ) :=
  {v | ∃ c : Fin 4, v (Sum.inl (Sum.inr 2))=(c.val : ℝ) ∧
    v (Sum.inr 1)=Fs c (Sum.elim (fun r => v (Sum.inl (Sum.inl r)))
      ![v (Sum.inl (Sum.inr 0)),v (Sum.inl (Sum.inr 1)),v (Sum.inr 0)])}

theorem jointOriginalArcScalarGraph_definable {α : Type} [Finite α]
    (Fs : Fin 4 → ((α ⊕ Fin 3) → ℝ) → ℝ)
    (hFs : ∀ c, HasPolynomialSignDescription
      (selectedFunctionGraph univ (fun p (_ : Unit) => Fs c p))) :
    (univ : Set ℝ).Definable Language.ring (jointOriginalArcScalarGraph Fs) := by
  let V := (α ⊕ Fin 3) ⊕ Fin 2
  let e : (α ⊕ Fin 3) ⊕ Unit → V :=
    Sum.elim (Sum.elim (fun r => Sum.inl (Sum.inl r))
      ![Sum.inl (Sum.inr 0),Sum.inl (Sum.inr 1),Sum.inr 0]) (fun _ => Sum.inr 1)
  have hc (c : Fin 4) : (univ : Set ℝ).Definable Language.ring
      {v : V → ℝ | v (Sum.inl (Sum.inr 2))=(c.val : ℝ) ∧
        v (Sum.inr 1)=Fs c (Sum.elim (fun r => v (Sum.inl (Sum.inl r)))
          ![v (Sum.inl (Sum.inr 0)),v (Sum.inl (Sum.inr 1)),v (Sum.inr 0)])} := by
    have hgraph := (hasPolynomialSignDescription_definable (hFs c)).preimage_comp e
    have heq : (univ : Set ℝ).Definable Language.ring
        {v : V → ℝ | v (Sum.inr 1)=Fs c (Sum.elim (fun r => v (Sum.inl (Sum.inl r)))
          ![v (Sum.inl (Sum.inr 0)),v (Sum.inl (Sum.inr 1)),v (Sum.inr 0)])} := by
      convert hgraph using 1
      ext v
      have he : (fun i => v (e (Sum.inl i))) =
          Sum.elim (fun r => v (Sum.inl (Sum.inl r)))
            ![v (Sum.inl (Sum.inr 0)),v (Sum.inl (Sum.inr 1)),v (Sum.inr 0)] := by
        funext i
        rcases i with i | i
        · rfl
        · fin_cases i <;> rfl
      simp only [mem_setOf_eq,mem_preimage,selectedFunctionGraph,mem_univ,true_and,
        Function.comp_def,he]
      constructor
      · intro h
        funext u
        cases u
        exact h.symm
      · intro h
        exact (congrFun h ()).symm
    have hcode := realPolynomial_zero_definable
      (MvPolynomial.X (Sum.inl (Sum.inr 2) : V)-MvPolynomial.C (c.val : ℝ))
    have hcode' : (univ : Set ℝ).Definable Language.ring
        {v : V → ℝ | v (Sum.inl (Sum.inr 2))=(c.val : ℝ)} := by
      simpa only [map_sub,MvPolynomial.eval_X,MvPolynomial.eval_C,sub_eq_zero] using hcode
    exact hcode'.inter heq
  have h := (realDefinable_finite_all (fun c : Fin 4 => (hc c).compl)).compl
  convert h using 1
  ext v
  change (∃ c : Fin 4, _) ↔ ¬ ∀ c : Fin 4, ¬ _
  simp only [not_forall,not_not]
  rfl

theorem jointOriginalArcScalarGraph_realize {α : Type*}
    (Fs : Fin 4 → ((α ⊕ Fin 3) → ℝ) → ℝ)
    (p : α → ℝ) (a b : ℝ) (d : Fin 4) (x y : ℝ) :
    Sum.elim (Sum.elim p ![a,b,(d.val : ℝ)]) ![x,y]∈jointOriginalArcScalarGraph Fs ↔
      y=Fs d (Sum.elim p ![a,b,x]) := by
  constructor
  · rintro ⟨c,hc,hy⟩
    have hc' : (d.val : ℝ)=(c.val : ℝ) := hc
    have he : c=d := Fin.ext (by exact_mod_cast hc'.symm)
    subst c
    exact hy
  · intro h
    exact ⟨d,rfl,h⟩

theorem SelectedOriginalPlanarArc.eqOn
    {g : ℝ → Fin 2 → ℝ} {a b : ℝ} {d : Fin 4} {F G : ℝ → ℝ}
    (hF : SelectedOriginalPlanarArc g a b d F)
    (hG : SelectedOriginalPlanarArc g a b d G) :
    EqOn F G (Icc (planarDirectionSign d*g a (planarDirectionI d))
      (planarDirectionSign d*g b (planarDirectionI d))) := by
  intro x hx
  obtain ⟨r,hr,he,hval⟩ := hF.2.2.2.2 x hx
  calc
    F x = g r (planarDirectionK d) := hval
    _ = G x := by rw [he]; exact (hG.2.2.2.1 r hr).symm

end PaperI
