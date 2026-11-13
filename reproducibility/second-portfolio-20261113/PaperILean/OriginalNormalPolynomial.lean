import PaperILean.OriginalNormalGraphCalculus
import PaperILean.DirectionalPolynomialDerivatives

/-! The actual normal derivatives of the full original coefficient phase.
No lower normal derivative is assumed to vanish. The final sheet theorem
retains the manuscript range 2 <= m <= floor(k/2).
-/
noncomputable section
namespace PaperI
open Filter
open scoped Topology

def originalNormalPolynomial {k : ℕ} (F : CoefficientSpace k) (n : ℕ) :
    MvPolynomial (Fin 3) ℝ :=
  iteratedPolynomialPartial n (fun _ => 0) (coefficientPolynomial F)

def originalNormalPhase {k : ℕ} (F : CoefficientSpace k) (n : ℕ) (x : PhysicalSpace) : ℝ :=
  iteratedFDeriv ℝ n (phase F) x (fun _ => Pi.single (0 : Fin 3) (1 : ℝ))

theorem originalNormalPhase_eq_eval {k : ℕ} (F : CoefficientSpace k) (n : ℕ) (x : PhysicalSpace) :
    originalNormalPhase F n x=MvPolynomial.eval x (originalNormalPolynomial F n) :=
  iteratedFDeriv_phase_coordinate F n x (fun _ => 0)

theorem originalNormalPolynomial_succ {k : ℕ} (F : CoefficientSpace k) (n : ℕ) :
    originalNormalPolynomial F (n+1)=MvPolynomial.pderiv 0 (originalNormalPolynomial F n) := rfl

theorem originalNormalPhase_contDiff {k : ℕ} (F : CoefficientSpace k) (n : ℕ) (d : WithTop ℕ∞) :
    ContDiff ℝ d (originalNormalPhase F n) := by
  have he : originalNormalPhase F n=(fun x => MvPolynomial.eval x (originalNormalPolynomial F n)) :=
    funext (originalNormalPhase_eq_eval F n)
  rw [he]
  exact contDiff_evalPolynomial _ d

theorem originalNormal_x_basis : (Pi.single (0 : Fin 3) (1 : ℝ))=![1,0,0] := by
  ext i
  fin_cases i <;> simp [Pi.single_apply]

theorem originalNormal_y_basis : (Pi.single (1 : Fin 3) (1 : ℝ))=![0,1,0] := by
  ext i
  fin_cases i <;> simp [Pi.single_apply]

theorem originalNormalPhase_partial {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (x : PhysicalSpace) (j : Fin 3) :
    fderiv ℝ (originalNormalPhase F n) x (Pi.single j 1)=
      MvPolynomial.eval x (MvPolynomial.pderiv j (originalNormalPolynomial F n)) := by
  have he : originalNormalPhase F n=(fun u => MvPolynomial.eval u (originalNormalPolynomial F n)) :=
    funext (originalNormalPhase_eq_eval F n)
  rw [he]
  exact fderiv_evalPolynomial_single _ x j

theorem originalNormalPhase_dx {k : ℕ} (F : CoefficientSpace k) (n : ℕ) (x : PhysicalSpace) :
    fderiv ℝ (originalNormalPhase F n) x ![1,0,0]=originalNormalPhase F (n+1) x := by
  rw [← originalNormal_x_basis,originalNormalPhase_partial,originalNormalPhase_eq_eval,
    originalNormalPolynomial_succ]

theorem originalNormalPolynomial_totalDegree {k : ℕ} (F : CoefficientSpace k) (n : ℕ) :
    (originalNormalPolynomial F n).totalDegree≤k-n := by
  induction n with
  | zero => exact coefficientPolynomial_totalDegree F
  | succ n ih =>
    rw [originalNormalPolynomial_succ]
    exact (totalDegree_polynomialPartial_le 0 _).trans
      (by simpa only [Nat.sub_sub] using Nat.sub_le_sub_right ih 1)

theorem originalNormal_manuscript_sheet {k : ℕ} (F : CoefficientSpace k) (m : ℕ)
    (hm : 2≤m) (hmk : m≤k/2) (x y z : ℝ)
    (hzero : originalNormalPhase F (m-1) ![x,y,z]=0)
    (hk : originalNormalPhase F m ![x,y,z]≠0) :
    ∃ c : (Fin 2 → ℝ) → ℝ, c ![y,z]=x ∧ ContDiffAt ℝ 2 c ![y,z] ∧
      (∀ᶠ w in 𝓝 (![y,z] : Fin 2 → ℝ), originalNormalPhase F (m-1) ![c w,w 0,w 1]=0) ∧
      (∀ᶠ u in 𝓝 (![x,y,z] : Fin 3 → ℝ),
        originalNormalPhase F (m-1) u=0 → u 0=c ![u 1,u 2]) := by
  have horder : m-1+1=m := by omega
  have hdx : fderiv ℝ (originalNormalPhase F (m-1)) ![x,y,z] ![1,0,0]≠0 := by
    rwa [originalNormalPhase_dx,horder]
  exact originalNormal_local_graph (originalNormalPhase F (m-1)) x ![y,z]
    (originalNormalPhase_contDiff F (m-1) 2).contDiffAt hzero hdx

def originalGaussSecondPolynomial {k : ℕ} (F : CoefficientSpace k) (n : ℕ) (p : ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.pderiv 1 (originalNormalPolynomial F n)+p • MvPolynomial.pderiv 0 (originalNormalPolynomial F n)

theorem originalGaussSecondPolynomial_eval {k : ℕ} (F : CoefficientSpace k) (n : ℕ) (p : ℝ)
    (x : PhysicalSpace) :
    MvPolynomial.eval x (originalGaussSecondPolynomial F n p)=
      fderiv ℝ (originalNormalPhase F n) x ![0,1,0]+
        p*fderiv ℝ (originalNormalPhase F n) x ![1,0,0] := by
  rw [← originalNormal_x_basis,← originalNormal_y_basis,originalNormalPhase_partial,
    originalNormalPhase_partial]
  simp [originalGaussSecondPolynomial]

theorem originalGaussSecondPolynomial_totalDegree {k : ℕ} (F : CoefficientSpace k) (n : ℕ) (p : ℝ) :
    (originalGaussSecondPolynomial F n p).totalDegree≤k-n-1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_polynomialPartial_le 1 _).trans
      (Nat.sub_le_sub_right (originalNormalPolynomial_totalDegree F n) 1)
  · exact (MvPolynomial.totalDegree_smul_le p _).trans ((totalDegree_polynomialPartial_le 0 _).trans
      (Nat.sub_le_sub_right (originalNormalPolynomial_totalDegree F n) 1))

end PaperI
