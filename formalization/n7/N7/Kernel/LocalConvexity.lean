import N7.Kernel.GapAnalytic

set_option autoImplicit false
namespace N7.Kernel
open Matrix Set
namespace GapAnalytic

theorem face_quadratic_nonneg (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : (A.submatrix Fin.succ Fin.succ).PosSemidef)
    (w : Fin 3 → ℝ) (hw : w 0=0) : 0≤w ⬝ᵥ (A*ᵥw) := by
  have h := hA.dotProduct_mulVec_nonneg (fun i : Fin 2 => w i.succ)
  simpa [dotProduct,Matrix.mulVec,Matrix.submatrix,Fin.sum_univ_succ,hw] using h

/-- Convexity is required only in the tangent plane, not in the omitted u direction. -/
theorem gap_nonneg_of_face_segment (p : ExactKernel) (c x : Fin 3 → ℝ)
    (hc : c 0=0) (hx : x 0=0)
    (h0 : gap p c=0) (hg : 0≤∑ i,gradient p c i*(x i-c i))
    (hd : ∀ s ∈ Icc (0:ℝ) 1,distance (line c (x-c) s)≠0)
    (hh : ∀ s ∈ Icc (0:ℝ) 1, ∀ w : Fin 3 → ℝ, w 0=0 →
      0≤w ⬝ᵥ (hessian p (line c (x-c) s)*ᵥw)) : 0≤gap p x := by
  apply gap_nonneg_of_segment_quadratic p c x h0 hg hd
  intro s hs
  apply hh s hs (x-c)
  simp [hx,hc]

def face0 (x : Fin 3 → ℝ) : Fin 3 → ℝ := ![0,x 1,x 2]

/-- Monotonicity in u extends a two-dimensional face bound to u≥0. -/
theorem gap_nonneg_of_face0 (p : ExactKernel) (x : Fin 3 → ℝ)
    (hx : 0≤x 0) (hface : 0≤gap p (face0 x))
    (hd : ∀ s ∈ Icc (0:ℝ) 1,distance (line (face0 x) (x-face0 x) s)≠0)
    (hg : ∀ s ∈ Icc (0:ℝ) 1,0≤gradient p (line (face0 x) (x-face0 x) s) 0) :
    0≤gap p x := by
  have hf : MonotoneOn (curveF p (face0 x) (x-face0 x)) (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro s hs
      exact (curveF_hasDerivAt p (face0 x) (x-face0 x) s (hd s hs)).continuousAt.continuousWithinAt
    · intro s hs
      exact (curveF_hasDerivAt p (face0 x) (x-face0 x) s
        (hd s (interior_subset hs))).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Icc (0:ℝ) 1 := interior_subset hs
      rw [(curveF_hasDerivAt p (face0 x) (x-face0 x) s (hd s hs')).deriv]
      simpa [curveGradient,face0,Fin.sum_univ_succ] using mul_nonneg (hg s hs') hx
  have h := hf (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1)
    (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1) (by norm_num)
  have h0 : line (face0 x) (x-face0 x) 0=face0 x := by ext i; simp [line]
  have h1 : line (face0 x) (x-face0 x) 1=x := by ext i; simp [line]
  simp only [curveF,h0,h1] at h
  exact hface.trans h

def gram (x : Fin 3 → ℝ) : ℝ := x 0*x 1-(x 2)^2

/-- μ is a full exact log coefficient; it need not be rational. -/
def subtractGram (p : ExactKernel) (μ : KernelCoeff) : ExactKernel :=
  p ++ [⟨1,1,0,-μ⟩,⟨0,0,2,μ⟩]

theorem eval3_append (p q : ExactKernel) (x : Fin 3 → ℝ) :
    eval3 (p++q) x=eval3 p x+eval3 q x := by
  induction p with
  | nil => simp [eval3,ExactKernel.real]
  | cons a p ih =>
    simp only [List.cons_append,eval3,ExactKernel.real] at ih ⊢
    rw [ih]
    ring

theorem eval3_subtractGram (p : ExactKernel) (μ : KernelCoeff) (x : Fin 3 → ℝ) :
    eval3 (subtractGram p μ) x=eval3 p x-μ.real*gram x := by
  rw [subtractGram,eval3_append]
  simp only [eval3,ExactKernel.real,KernelTerm.real,KernelCoeff.real_neg,pow_zero,pow_one]
  unfold gram
  ring

theorem gap_subtractGram (p : ExactKernel) (μ : KernelCoeff) (x : Fin 3 → ℝ) :
    gap (subtractGram p μ) x=gap p x-μ.real*gram x := by
  rw [gap,eval3_subtractGram]
  unfold gap
  ring

theorem gap_nonneg_of_gram_correction (p : ExactKernel) (μ : KernelCoeff)
    (x : Fin 3 → ℝ) (hμ : 0≤μ.real) (hx : 0≤gram x)
    (hcorrected : 0≤gap (subtractGram p μ) x) : 0≤gap p x := by
  rw [gap_subtractGram] at hcorrected
  linarith [mul_nonneg hμ hx]

#print axioms gap_nonneg_of_face_segment
#print axioms gap_nonneg_of_face0
#print axioms gap_nonneg_of_gram_correction
end GapAnalytic
end N7.Kernel
