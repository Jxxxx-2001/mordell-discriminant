import N7.Kernel.LocalGeometry
set_option autoImplicit false
namespace N7.Kernel.LocalGeometry
open GapAnalytic Set Matrix

theorem gap_nonneg_near (p : ExactKernel) (c : Fin 3 → ℚ) (r : ℚ)
    (hc : 0<centerDistance c-4*r) (h0 : gap p (point c)=0)
    (hg : ∀ i,gradient p (point c) i=0)
    (hh : ∀ x,Near c r x → (hessian p x).PosSemidef)
    {x : Fin 3 → ℝ} (hn : Near c r x) : 0≤gap p x := by
  apply gap_nonneg_of_segment p (point c) x h0
  · simp only [hg,zero_mul,Finset.sum_const_zero,le_refl]
  · intro s hs
    exact (near_distance_pos hc (near_line hn hs)).ne'
  · intro s hs
    exact hh _ (near_line hn hs)

theorem near_face0 {c : Fin 3 → ℚ} {r : ℚ} {x : Fin 3 → ℝ}
    (hc : c 0=0) (hr : 0≤r) (hn : Near c r x) : Near c r (face0 x) := by
  intro i
  fin_cases i
  · simpa [face0,hc] using (show (0:ℝ)≤(r:ℝ) by exact_mod_cast hr)
  · simpa [face0] using hn 1
  · simpa [face0,Matrix.cons_val_two] using hn 2

theorem near_face0_line {c : Fin 3 → ℚ} {r : ℚ} {x : Fin 3 → ℝ}
    (hc : c 0=0) (hn : Near c r x) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    Near c r (line (face0 x) (x-face0 x) s) := by
  intro i
  fin_cases i
  · have hx : |x 0|≤(r:ℝ) := by simpa [hc] using hn 0
    change |(0:ℝ)+s*(x 0-0)-(c 0:ℝ)|≤(r:ℝ)
    rw [hc]
    simp only [Rat.cast_zero,sub_zero,zero_add]
    rw [abs_mul,abs_of_nonneg hs.1]
    simpa using mul_le_mul hs.2 hx (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  · simpa [line,face0] using hn 1
  · simpa [line,face0,Matrix.cons_val_two] using hn 2

#print axioms gap_nonneg_near
end N7.Kernel.LocalGeometry
