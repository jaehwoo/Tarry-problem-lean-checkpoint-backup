import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Finite scalar normalization fibers for the complete part (i) at I3258--I3274.
The scalar data are arbitrary; the literal polynomial bridge supplies their
actual gradient and Hessian values. No finite-fiber contract is an input. -/

noncomputable section
namespace PaperI.NormalFibers

open Polynomial

/-- The literal normalizing equations, in source order `(c,a,b,d)`. -/
def scalarFrames (p : Polynomial ℝ)
    (gy gz xx xy xz yy yz zz : ℝ → ℝ) : Set (Fin 4 → ℝ) :=
  {w | p.eval (w 0) = 0 ∧ p.derivative.eval (w 0) ≠ 0 ∧
    w 1 * p.derivative.eval (w 0) + gy (w 0) = 0 ∧
    w 2 * p.derivative.eval (w 0) + w 3 * gy (w 0) + gz (w 0) = 0 ∧
    (((w 1 * w 2 * xx (w 0) + (w 1 * w 3 + w 2) * xy (w 0) +
        w 1 * xz (w 0) + w 3 * yy (w 0) + yz (w 0)) = 0 ∧
      (w 1 ^ 2 * xx (w 0) + 2 * w 1 * xy (w 0) + yy (w 0)) ≠ 0) ∨
     ((w 2 ^ 2 * xx (w 0) + 2 * w 2 * w 3 * xy (w 0) +
        2 * w 2 * xz (w 0) + w 3 ^ 2 * yy (w 0) +
        2 * w 3 * yz (w 0) + zz (w 0)) = 0 ∧
      (w 1 * w 2 * xx (w 0) + (w 1 * w 3 + w 2) * xy (w 0) +
        w 1 * xz (w 0) + w 3 * yy (w 0) + yz (w 0)) ≠ 0))}

/-- The first chart's actual shear polynomial. -/
def linePoly (u t : ℝ) : Polynomial ℝ := C t + C u * X

/-- The second chart's actual shear polynomial. -/
def quadPoly (u t v : ℝ) : Polynomial ℝ := C v + C (2 * t) * X + C u * X ^ 2

theorem linePoly_eval (u t d : ℝ) : (linePoly u t).eval d = t + d * u := by
  simp [linePoly]
  ring

theorem quadPoly_eval (u t v d : ℝ) :
    (quadPoly u t v).eval d = v + 2 * d * t + d ^ 2 * u := by
  simp [quadPoly]
  ring

theorem quadPoly_derivative_eval (u t v d : ℝ) :
    (quadPoly u t v).derivative.eval d = 2 * (t + d * u) := by
  simp [quadPoly]
  ring

theorem linePoly_natDegree_le (u t : ℝ) : (linePoly u t).natDegree ≤ 1 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le u 1

theorem quadPoly_natDegree_le (u t v : ℝ) : (quadPoly u t v).natDegree ≤ 2 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (linePoly_natDegree_le (2 * t) v).trans (by omega)
  · exact Polynomial.natDegree_C_mul_X_pow_le u 2

/-- A finite containing set of legal shears, including all degenerate cases. -/
def shearCandidates (u t v : ℝ) : Finset ℝ :=
  (linePoly u t).roots.toFinset ∪ (quadPoly u t v).roots.toFinset

theorem shearCandidates_card_le (u t v : ℝ) : (shearCandidates u t v).card ≤ 3 := by
  have h₁ : (linePoly u t).roots.toFinset.card ≤ 1 :=
    (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (linePoly_natDegree_le u t))
  have h₂ : (quadPoly u t v).roots.toFinset.card ≤ 2 :=
    (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (quadPoly_natDegree_le u t v))
  exact (Finset.card_union_le _ _).trans (by omega)

theorem mem_shearCandidates {u t v d : ℝ}
    (h : (t + d * u = 0 ∧ u ≠ 0) ∨
      (v + 2 * d * t + d ^ 2 * u = 0 ∧ t + d * u ≠ 0)) :
    d ∈ shearCandidates u t v := by
  classical
  rcases h with ⟨hd, hu⟩ | ⟨hd, hp⟩
  · have hpoly : linePoly u t ≠ 0 := by
      intro hz
      have hc := congrArg (fun q : Polynomial ℝ => q.coeff 1) hz
      apply hu
      simpa [linePoly] using hc
    apply Finset.mem_union_left
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hpoly).mpr
    exact (linePoly_eval u t d).trans hd
  · have hpoly : quadPoly u t v ≠ 0 := by
      intro hz
      have hc := congrArg (fun q : Polynomial ℝ => q.derivative.eval d) hz
      dsimp only at hc
      rw [quadPoly_derivative_eval] at hc
      simp only [Polynomial.derivative_zero, Polynomial.eval_zero] at hc
      apply hp
      linarith
    apply Finset.mem_union_right
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hpoly).mpr
    exact (quadPoly_eval u t v d).trans hd

/-- Reconstructing `a,b` after fixing the normal root and shear. -/
def reconstruct (c a₀ b₀ d : ℝ) : Fin 4 → ℝ := ![c, a₀, b₀ + d * a₀, d]

/-- The scalar normalization solution set is genuinely finite, with no input
cardinality or derivative contract. The literal `G` bridge consumes it directly. -/
theorem scalarFrames_finite_ncard (p : Polynomial ℝ)
    (gy gz xx xy xz yy yz zz : ℝ → ℝ) :
    (scalarFrames p gy gz xx xy xz yy yz zz).Finite ∧
      (scalarFrames p gy gz xx xy xz yy yz zz).ncard ≤ 3 * p.natDegree := by
  classical
  let a₀ : ℝ → ℝ := fun c => -gy c / p.derivative.eval c
  let b₀ : ℝ → ℝ := fun c => -gz c / p.derivative.eval c
  let U : ℝ → ℝ := fun c => a₀ c ^ 2 * xx c + 2 * a₀ c * xy c + yy c
  let T : ℝ → ℝ := fun c =>
    a₀ c * b₀ c * xx c + b₀ c * xy c + a₀ c * xz c + yz c
  let V : ℝ → ℝ := fun c => b₀ c ^ 2 * xx c + 2 * b₀ c * xz c + zz c
  let localCandidates : ℝ → Finset (Fin 4 → ℝ) := fun c =>
    (shearCandidates (U c) (T c) (V c)).image (reconstruct c (a₀ c) (b₀ c))
  let candidates : Finset (Fin 4 → ℝ) := p.roots.toFinset.biUnion localCandidates
  have hlocal (c : ℝ) : (localCandidates c).card ≤ 3 :=
    Finset.card_image_le.trans (shearCandidates_card_le (U c) (T c) (V c))
  have hcandidates : candidates.card ≤ 3 * p.natDegree := by
    have hc := Finset.card_biUnion_le_card_mul p.roots.toFinset localCandidates 3
      (fun c _ => hlocal c)
    have hr : p.roots.toFinset.card ≤ p.natDegree :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p)
    exact hc.trans (by omega)
  have hsub : scalarFrames p gy gz xx xy xz yy yz zz ⊆ (candidates : Set (Fin 4 → ℝ)) := by
    intro w hw
    rcases hw with ⟨hc, hLam, ha, hb, hchart⟩
    have hp : p ≠ 0 := by
      intro hz
      apply hLam
      simp [hz]
    have hcroot : w 0 ∈ p.roots.toFinset :=
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hc)
    have ha₀ : w 1 = a₀ (w 0) := by
      apply (eq_div_iff hLam).mpr
      linarith
    have hb₀ : w 2 = b₀ (w 0) + w 3 * a₀ (w 0) := by
      dsimp [a₀, b₀]
      rw [← mul_div_assoc, ← add_div]
      apply (eq_div_iff hLam).mpr
      linarith
    have hU : w 1 ^ 2 * xx (w 0) + 2 * w 1 * xy (w 0) + yy (w 0) = U (w 0) := by
      rw [ha₀]
    have hT : w 1 * w 2 * xx (w 0) + (w 1 * w 3 + w 2) * xy (w 0) +
        w 1 * xz (w 0) + w 3 * yy (w 0) + yz (w 0) = T (w 0) + w 3 * U (w 0) := by
      rw [ha₀, hb₀]
      dsimp [U, T]
      ring
    have hV : w 2 ^ 2 * xx (w 0) + 2 * w 2 * w 3 * xy (w 0) +
        2 * w 2 * xz (w 0) + w 3 ^ 2 * yy (w 0) +
        2 * w 3 * yz (w 0) + zz (w 0) =
          V (w 0) + 2 * w 3 * T (w 0) + w 3 ^ 2 * U (w 0) := by
      rw [hb₀]
      dsimp [U, T, V]
      ring
    have hd : w 3 ∈ shearCandidates (U (w 0)) (T (w 0)) (V (w 0)) := by
      apply mem_shearCandidates
      rcases hchart with ⟨ht, hu⟩ | ⟨hv, ht⟩
      · exact Or.inl ⟨hT.symm.trans ht, fun h => hu (hU.trans h)⟩
      · exact Or.inr ⟨hV.symm.trans hv, fun h => ht (hT.trans h)⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨w 0, hcroot, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨w 3, hd, ?_⟩
    funext i
    fin_cases i <;> simp [reconstruct, ha₀, hb₀]
  refine ⟨candidates.finite_toSet.subset hsub, ?_⟩
  exact (Set.ncard_le_ncard hsub candidates.finite_toSet).trans
    (by simpa using hcandidates)

end PaperI.NormalFibers
