import N7.Kernel.LocalConvexity
import N7.Kernel.Bernstein.HornerBounds

set_option autoImplicit false
namespace N7.Kernel.LocalGeometry
open Checks Matrix Set GapAnalytic
set_option maxHeartbeats 1200000

def point (c : Fin 3 → ℚ) : Fin 3 → ℝ := fun i => c i
def Near (c : Fin 3 → ℚ) (r : ℚ) (x : Fin 3 → ℝ) : Prop := ∀ i, |x i-c i|≤(r:ℝ)
def centerDistance (c : Fin 3 → ℚ) : ℚ := c 0+c 1-2*c 2
def invDistance (c : Fin 3 → ℚ) (r : ℚ) : QInterval :=
  ⟨1/(centerDistance c+4*r),1/(centerDistance c-4*r)⟩
def invDistanceSq (c : Fin 3 → ℚ) (r : ℚ) : QInterval :=
  ⟨1/(centerDistance c+4*r)^2,1/(centerDistance c-4*r)^2⟩
def ddQ : Fin 3 → ℚ := ![1,1,-2]

theorem ddQ_cast (i : Fin 3) : (ddQ i:ℝ)=dd i := by
  fin_cases i <;> norm_num [ddQ,dd,Matrix.cons_val_two]

theorem near_distance_bounds {c : Fin 3 → ℚ} {r : ℚ} {x : Fin 3 → ℝ}
    (hn : Near c r x) :
    ((centerDistance c-4*r:ℚ):ℝ)≤distance x ∧ distance x≤((centerDistance c+4*r:ℚ):ℝ) := by
  have hu := abs_le.mp (hn 0)
  have hv := abs_le.mp (hn 1)
  have ht := abs_le.mp (hn 2)
  dsimp [distance,centerDistance]
  push_cast
  constructor <;> linarith

theorem near_distance_pos {c : Fin 3 → ℚ} {r : ℚ} {x : Fin 3 → ℝ}
    (hc : 0<centerDistance c-4*r) (hn : Near c r x) : 0<distance x := by
  have h : (0:ℝ)<((centerDistance c-4*r:ℚ):ℝ) := by exact_mod_cast hc
  exact h.trans_le (near_distance_bounds hn).1

theorem invDistance_sound {c : Fin 3 → ℚ} {r : ℚ} {x : Fin 3 → ℝ}
    (hc : 0<centerDistance c-4*r) (hn : Near c r x) :
    (invDistance c r).Contains (1/distance x) := by
  have h := near_distance_bounds hn
  have hp := near_distance_pos hc hn
  have hmin : (0:ℝ)<((centerDistance c-4*r:ℚ):ℝ) := by exact_mod_cast hc
  have lo := one_div_le_one_div_of_le hp h.2
  have hi := one_div_le_one_div_of_le hmin h.1
  simpa only [invDistance,QInterval.Contains,Rat.cast_div,Rat.cast_one] using And.intro lo hi

theorem invDistanceSq_sound {c : Fin 3 → ℚ} {r : ℚ} {x : Fin 3 → ℝ}
    (hc : 0<centerDistance c-4*r) (hn : Near c r x) :
    (invDistanceSq c r).Contains (1/(distance x)^2) := by
  have h := near_distance_bounds hn
  have hp := near_distance_pos hc hn
  have hmin : (0:ℝ)<((centerDistance c-4*r:ℚ):ℝ) := by exact_mod_cast hc
  have sl : (((centerDistance c-4*r:ℚ):ℝ))^2≤(distance x)^2 := by nlinarith [h.1]
  have sh : (distance x)^2≤(((centerDistance c+4*r:ℚ):ℝ))^2 := by nlinarith [h.2]
  have lo := one_div_le_one_div_of_le (sq_pos_of_pos hp) sh
  have hi := one_div_le_one_div_of_le (sq_pos_of_pos hmin) sl
  simpa only [invDistanceSq,QInterval.Contains,Rat.cast_div,Rat.cast_one,Rat.cast_pow] using And.intro lo hi

def hessianBounds {n : ℕ} (c : Fin 3 → ℚ) (r : ℚ)
    (indices : Fin n → Fin 3) (polys : Fin n → Fin n → DenseKernel)
    (i j : Fin n) : QInterval :=
  ((polys i j).bound r).add ((invDistanceSq c r).scale (ddQ (indices i)*ddQ (indices j)))

theorem hessianBounds_sound {n : ℕ} (p : ExactKernel) (c : Fin 3 → ℚ) (r : ℚ)
    (indices : Fin n → Fin 3) (polys : Fin n → Fin n → DenseKernel)
    (hpoly : ∀ i j x, (polys i j).real (x 0-c 0) (x 1-c 1) (x 2-c 2)=
      eval3 (partialPoly (partialPoly p (indices i)) (indices j)) x)
    (hc : 0<centerDistance c-4*r) {x : Fin 3 → ℝ} (hn : Near c r x) (i j : Fin n) :
    (hessianBounds c r indices polys i j).Contains (hessian p x (indices i) (indices j)) := by
  have hp := DenseKernel.bound_sound r (polys i j) _ _ _ (hn 0) (hn 1) (hn 2)
  rw [hpoly] at hp
  have h := QInterval.add_sound hp
    (QInterval.scale_sound (ddQ (indices i)*ddQ (indices j)) (invDistanceSq_sound hc hn))
  convert h using 1
  dsimp [hessian]
  push_cast
  rw [ddQ_cast,ddQ_cast]
  ring

def gradientUBounds (c : Fin 3 → ℚ) (r : ℚ) (poly : DenseKernel) : QInterval :=
  (poly.bound r).add ((invDistance c r).scale (-1))

theorem gradientUBounds_sound (p : ExactKernel) (c : Fin 3 → ℚ) (r : ℚ)
    (poly : DenseKernel)
    (hpoly : ∀ x, poly.real (x 0-c 0) (x 1-c 1) (x 2-c 2)=eval3 p.du x)
    (hc : 0<centerDistance c-4*r) {x : Fin 3 → ℝ} (hn : Near c r x) :
    (gradientUBounds c r poly).Contains (gradient p x 0) := by
  have hp := DenseKernel.bound_sound r poly _ _ _ (hn 0) (hn 1) (hn 2)
  rw [hpoly] at hp
  have h := QInterval.add_sound hp (QInterval.scale_sound (-1) (invDistance_sound hc hn))
  convert h using 1
  simp [gradient,partialPoly,dd]
  ring

theorem near_line {c : Fin 3 → ℚ} {r : ℚ} {x : Fin 3 → ℝ}
    (hn : Near c r x) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    Near c r (line (point c) (x-point c) s) := by
  intro i
  change |(c i:ℝ)+s*(x i-c i)-c i|≤(r:ℝ)
  rw [show (c i:ℝ)+s*(x i-c i)-c i=s*(x i-c i) by ring,abs_mul,abs_of_nonneg hs.1]
  simpa using mul_le_mul hs.2 (hn i) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)

#print axioms hessianBounds_sound
end N7.Kernel.LocalGeometry
