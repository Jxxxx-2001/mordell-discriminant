import N7.Kernel.KernelCurves
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace N7.Kernel
namespace GapAnalytic
open Matrix Set
set_option maxHeartbeats 0

def partialPoly (p : ExactKernel) (i : Fin 3) : ExactKernel :=
  if i=0 then p.du else if i=1 then p.dv else p.dt
noncomputable def eval3 (p : ExactKernel) (x : Fin 3 → ℝ) : ℝ := p.real (x 0) (x 1) (x 2)
def distance (x : Fin 3 → ℝ) : ℝ := x 0+x 1-2*x 2
def dd : Fin 3 → ℝ := ![1,1,-2]
noncomputable def gap (p : ExactKernel) (x : Fin 3 → ℝ) : ℝ := eval3 p x-Real.log (distance x)
noncomputable def gradient (p : ExactKernel) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  eval3 (partialPoly p i) x-dd i/distance x
noncomputable def hessian (p : ExactKernel) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => eval3 (partialPoly (partialPoly p i) j) x+dd i*dd j/(distance x)^2
def line (c w : Fin 3 → ℝ) (s : ℝ) : Fin 3 → ℝ := fun i => c i+s*w i
noncomputable def curveF (p : ExactKernel) (c w : Fin 3 → ℝ) (s : ℝ) : ℝ := gap p (line c w s)
noncomputable def curveGradient (p : ExactKernel) (c w : Fin 3 → ℝ) (s : ℝ) : ℝ :=
  ∑ i, gradient p (line c w s) i*w i

theorem line_coord_hasDerivAt (c w : Fin 3 → ℝ) (s : ℝ) (i : Fin 3) :
    HasDerivAt (fun z => line c w z i) (w i) s := by
  simpa [line] using ((hasDerivAt_id s).mul_const (w i)).const_add (c i)

theorem line_distance_hasDerivAt (c w : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (fun z => distance (line c w z)) (w 0+w 1-2*w 2) s :=
  ((line_coord_hasDerivAt c w s 0).add (line_coord_hasDerivAt c w s 1)).sub
    ((line_coord_hasDerivAt c w s 2).const_mul 2)

theorem curveF_hasDerivAt (p : ExactKernel) (c w : Fin 3 → ℝ) (s : ℝ)
    (hd : distance (line c w s)≠0) :
    HasDerivAt (curveF p c w) (curveGradient p c w s) s := by
  have hp := p.hasDerivAt_path (fun z => line c w z 0) (fun z => line c w z 1)
    (fun z => line c w z 2) (w 0) (w 1) (w 2) s
    (line_coord_hasDerivAt c w s 0) (line_coord_hasDerivAt c w s 1) (line_coord_hasDerivAt c w s 2)
  have h := hp.sub ((line_distance_hasDerivAt c w s).log hd)
  convert h using 1
  simp [curveGradient,gradient,eval3,partialPoly,dd,Fin.sum_univ_succ]
  ring

theorem line_gradient_hasDerivAt (p : ExactKernel) (c w : Fin 3 → ℝ) (s : ℝ) (i : Fin 3)
    (hd : distance (line c w s)≠0) :
    HasDerivAt (fun z => gradient p (line c w z) i)
      (∑ j,hessian p (line c w s) i j*w j) s := by
  have hp := (partialPoly p i).hasDerivAt_path
    (fun z => line c w z 0) (fun z => line c w z 1) (fun z => line c w z 2)
    (w 0) (w 1) (w 2) s
    (line_coord_hasDerivAt c w s 0) (line_coord_hasDerivAt c w s 1) (line_coord_hasDerivAt c w s 2)
  have h := hp.sub (((line_distance_hasDerivAt c w s).inv hd).const_mul (dd i))
  convert h using 1
  simp [hessian,partialPoly,eval3,dd,Fin.sum_univ_succ]
  fin_cases i <;> simp [dd] <;> ring

theorem curveGradient_hasDerivAt (p : ExactKernel) (c w : Fin 3 → ℝ) (s : ℝ)
    (hd : distance (line c w s)≠0) :
    HasDerivAt (curveGradient p c w)
      (w ⬝ᵥ (hessian p (line c w s)*ᵥw)) s := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (line_gradient_hasDerivAt p c w s i hd).mul_const (w i))
  convert h using 1
  simp only [dotProduct,Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem mixed_partials (p : ExactKernel) (i j : Fin 3) (x : Fin 3 → ℝ) :
    eval3 (partialPoly (partialPoly p i) j) x=eval3 (partialPoly (partialPoly p j) i) x := by
  fin_cases i <;> fin_cases j <;> dsimp [partialPoly]
  all_goals
    induction p with
    | nil => rfl
    | cons s ss ih =>
      simp only [eval3,ExactKernel.du,ExactKernel.dv,ExactKernel.dt,List.map_cons,ExactKernel.real] at ih ⊢
      rw [ih]
      congr 1
      simp only [KernelTerm.real,KernelTerm.du,KernelTerm.dv,KernelTerm.dt,
        KernelCoeff.real_scale,Rat.cast_natCast]
      ring

theorem hessian_isHermitian (p : ExactKernel) (x : Fin 3 → ℝ) : (hessian p x).IsHermitian := by
  change (hessian p x).conjTranspose=hessian p x
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,hessian]
  rw [mixed_partials p j i x]
  ring

/-- Includes boundary contacts: the initial directional derivative need only be nonnegative. -/
theorem gap_nonneg_of_segment_quadratic (p : ExactKernel) (c x : Fin 3 → ℝ)
    (h0 : gap p c=0) (hg : 0≤∑ i,gradient p c i*(x i-c i))
    (hd : ∀ s ∈ Icc (0:ℝ) 1,distance (line c (x-c) s)≠0)
    (hh : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ (x-c) ⬝ᵥ (hessian p (line c (x-c) s)*ᵥ(x-c))) :
    0≤gap p x := by
  have hm : MonotoneOn (curveGradient p c (x-c)) (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro s hs
      exact (curveGradient_hasDerivAt p c (x-c) s (hd s hs)).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Icc (0:ℝ) 1 := interior_subset hs
      exact (curveGradient_hasDerivAt p c (x-c) s (hd s hs' )).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Icc (0:ℝ) 1 := interior_subset hs
      rw [(curveGradient_hasDerivAt p c (x-c) s (hd s hs')).deriv]
      exact hh s hs'
  have hl0 : line c (x-c) 0=c := by ext i; simp [line]
  have hg0 : 0≤curveGradient p c (x-c) 0 := by simpa [curveGradient,hl0] using hg
  have hf : MonotoneOn (curveF p c (x-c)) (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro s hs
      exact (curveF_hasDerivAt p c (x-c) s (hd s hs)).continuousAt.continuousWithinAt
    · intro s hs
      exact (curveF_hasDerivAt p c (x-c) s (hd s (interior_subset hs) )).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Icc (0:ℝ) 1 := interior_subset hs
      rw [(curveF_hasDerivAt p c (x-c) s (hd s hs')).deriv]
      exact hg0.trans (hm (by norm_num) hs' hs'.1)
  have h := hf (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1)
    (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1) (by norm_num)
  have hl1 : line c (x-c) 1=x := by ext i; simp [line]
  simpa only [curveF,hl0,hl1,h0] using h

/-- Convenient full-PSD specialization; restricted slice proofs use the directional form. -/
theorem gap_nonneg_of_segment (p : ExactKernel) (c x : Fin 3 → ℝ)
    (h0 : gap p c=0) (hg : 0≤∑ i,gradient p c i*(x i-c i))
    (hd : ∀ s ∈ Icc (0:ℝ) 1,distance (line c (x-c) s)≠0)
    (hh : ∀ s ∈ Icc (0:ℝ) 1,(hessian p (line c (x-c) s)).PosSemidef) :
    0≤gap p x := by
  apply gap_nonneg_of_segment_quadratic p c x h0 hg hd
  intro s hs
  simpa only [star_trivial] using (hh s hs).dotProduct_mulVec_nonneg (x-c)

end GapAnalytic
end N7.Kernel

