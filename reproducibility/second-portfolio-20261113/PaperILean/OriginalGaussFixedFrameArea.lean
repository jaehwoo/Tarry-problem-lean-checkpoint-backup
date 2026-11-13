import PaperILean.PlanarRelativeEndpoints

/-! I436/I1309/I1323: the original upper-affine coordinates and their Gauss
projection. The candidate-area implication retains explicit initial-comparison
and localization premises. Their actual root-chart application is separate. -/
noncomputable section
namespace PaperI
open Set Metric MeasureTheory

def originalUpperAffineEval (g : Fin 6 → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 0+g 0*x 1+g 1*x 2+g 2,x 1+g 3*x 2+g 4,x 2+g 5]

def originalUpperAffineComp (g h : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![g 0+h 0,g 1+h 1+g 0*h 3,g 2+h 2+g 0*h 4+g 1*h 5,
    g 3+h 3,g 4+h 4+g 3*h 5,g 5+h 5]

def originalUpperAffineInv (g : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![-g 0,g 0*g 3-g 1,-g 2+g 0*g 4+g 1*g 5-g 0*g 3*g 5,
    -g 3,g 3*g 5-g 4,-g 5]

theorem originalUpperAffineEval_comp (g h : Fin 6 → ℝ) (x : Fin 3 → ℝ) :
    originalUpperAffineEval (originalUpperAffineComp g h) x =
      originalUpperAffineEval g (originalUpperAffineEval h x) := by
  funext i
  fin_cases i <;> simp [originalUpperAffineEval,originalUpperAffineComp] <;> ring

theorem originalUpperAffineComp_assoc (g h k : Fin 6 → ℝ) :
    originalUpperAffineComp (originalUpperAffineComp g h) k =
      originalUpperAffineComp g (originalUpperAffineComp h k) := by
  funext i
  fin_cases i <;> simp [originalUpperAffineComp] <;> ring

theorem originalUpperAffineComp_inv (g : Fin 6 → ℝ) :
    originalUpperAffineComp (originalUpperAffineInv g) g=0 ∧
      originalUpperAffineComp g (originalUpperAffineInv g)=0 := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [originalUpperAffineComp,originalUpperAffineInv] <;> ring

def originalGaussProjection (g : Fin 6 → ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![g 0,g 5]

theorem originalGaussProjection_comp (g h : Fin 6 → ℝ) :
    originalGaussProjection (originalUpperAffineComp g h) =
      originalGaussProjection g+originalGaussProjection h := by
  apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
  funext i
  fin_cases i <;> rfl

theorem originalGaussProjection_relative (g h : Fin 6 → ℝ) :
    originalGaussProjection (originalUpperAffineComp (originalUpperAffineInv g) h) =
      originalGaussProjection h-originalGaussProjection g := by
  apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
  funext i
  fin_cases i <;> simp [originalGaussProjection,originalUpperAffineComp,originalUpperAffineInv] <;> ring

def originalGaussCandidateProjection {ι : Type*}
    (a : ι → Fin 6 → ℝ) (S : ι → Set (Fin 6 → ℝ)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ i, (fun g => originalGaussProjection (originalUpperAffineComp (originalUpperAffineInv (a i)) g)) '' S i

theorem originalGaussCandidateProjection_subset_ball {ι : Type*}
    (a b : ι → Fin 6 → ℝ) (S : ι → Set (Fin 6 → ℝ)) (R L : ℝ)
    (hcomparison : ∀ i, dist (originalGaussProjection (b i)) (originalGaussProjection (a i))≤R*L)
    (hlocal : ∀ i g, g∈S i → dist (originalGaussProjection g) (originalGaussProjection (b i))≤2*L) :
    originalGaussCandidateProjection a S⊆closedBall 0 ((R+2)*L) := by
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨g,hg,rfl⟩ := hi
  change originalGaussProjection (originalUpperAffineComp (originalUpperAffineInv (a i)) g)∈_
  rw [originalGaussProjection_relative,mem_closedBall,dist_zero_right,← dist_eq_norm]
  exact (dist_triangle _ (originalGaussProjection (b i)) _).trans (by
    have hc := hcomparison i
    have hl := hlocal i g hg
    nlinarith)

theorem originalGaussCandidateProjection_area {ι : Type*}
    (a b : ι → Fin 6 → ℝ) (S : ι → Set (Fin 6 → ℝ))
    {R L : ℝ} (hR : 0≤R) (hL : 0≤L)
    (hcomparison : ∀ i, dist (originalGaussProjection (b i)) (originalGaussProjection (a i))≤R*L)
    (hlocal : ∀ i g, g∈S i → dist (originalGaussProjection g) (originalGaussProjection (b i))≤2*L) :
    volume (originalGaussCandidateProjection a S)≤ENNReal.ofReal (Real.pi*(R+2)^2*L^2) ∧
      volume (originalGaussCandidateProjection a S)≠⊤ ∧
      volume.real (originalGaussCandidateProjection a S)≤Real.pi*(R+2)^2*L^2 := by
  have hsub := originalGaussCandidateProjection_subset_ball a b S R L hcomparison hlocal
  have hhalf : 0≤(R+2)*L/2 := by positivity
  have harea := planar_area_of_subset_double_scale_ball hhalf
    (hsub.trans (closedBall_subset_closedBall (by linarith : (R+2)*L≤2*((R+2)*L/2))))
  have hbound : volume (originalGaussCandidateProjection a S)≤
      ENNReal.ofReal (Real.pi*(R+2)^2*L^2) := by
    convert harea using 1
    congr 1
    ring
  exact ⟨hbound,planar_finite_real_area_of_outer_bound (by positivity) hbound⟩

theorem translated_unit_balls_cover_plane :
    (⋃ x : EuclideanSpace ℝ (Fin 2), closedBall x (1:ℝ))=univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨x,by simp⟩

end PaperI
