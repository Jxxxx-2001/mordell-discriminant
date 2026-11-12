import Eight.CenterContact.Matrix
import Eight.ContactChecks.C0

namespace MordellEight.CenterContact
open Checks Matrix Set GapAnalytic
set_option maxHeartbeats 0
attribute [local irreducible] exactMajorant

def center : Fin 3 → ℝ := ![0,1,0]
def Near (x : Fin 3 → ℝ) : Prop := ∀ i,|x i-center i|≤(radius:ℝ)

theorem polynomial_real (i j : Fin 3) (x : Fin 3 → ℝ) :
    (polynomials i j).real (x 0) (x 1-1) (x 2)=
      eval3 (partialPoly (partialPoly exactMajorant i) j) x := by
  have h00 := H00.polynomial_real (x 0) (x 1-1) (x 2)
  have h01 := H01.polynomial_real (x 0) (x 1-1) (x 2)
  have h02 := H02.polynomial_real (x 0) (x 1-1) (x 2)
  have h11 := H11.polynomial_real (x 0) (x 1-1) (x 2)
  have h12 := H12.polynomial_real (x 0) (x 1-1) (x 2)
  have h22 := H22.polynomial_real (x 0) (x 1-1) (x 2)
  simp only [sub_add_cancel] at h00 h01 h02 h11 h12 h22
  have h10 := mixed_partials exactMajorant (0:Fin 3) 1 x
  have h20 := mixed_partials exactMajorant (0:Fin 3) 2 x
  have h21 := mixed_partials exactMajorant (1:Fin 3) 2 x
  fin_cases i <;> fin_cases j
  · simpa [polynomials,partialPoly,eval3,Matrix.cons_val_two] using h00
  · simpa [polynomials,partialPoly,eval3,Matrix.cons_val_two] using h01
  · simpa [polynomials,partialPoly,eval3,Matrix.cons_val_two] using h02
  · simpa [polynomials,partialPoly,eval3,Matrix.cons_val_two] using h01.trans h10
  · simpa [polynomials,partialPoly,eval3,Matrix.cons_val_two] using h11
  · simpa [polynomials,partialPoly,eval3,Matrix.cons_val_two] using h12
  · simpa [polynomials,partialPoly,eval3,Matrix.cons_val_two] using h02.trans h20
  · simpa [polynomials,partialPoly,eval3,Matrix.cons_val_two] using h12.trans h21
  · simpa [polynomials,partialPoly,eval3,Matrix.cons_val_two] using h22

theorem near_distance_bounds {x : Fin 3 → ℝ} (hn : Near x) :
    (1-4*radius:ℚ)≤distance x ∧ distance x≤(1+4*radius:ℚ) := by
  have hu := abs_le.mp (hn 0)
  have hv := abs_le.mp (hn 1)
  have ht := abs_le.mp (hn 2)
  norm_num [center,Matrix.cons_val_two] at hu hv ht
  dsimp [distance]
  push_cast
  constructor <;> linarith

theorem near_distance_pos {x : Fin 3 → ℝ} (hn : Near x) : 0<distance x := by
  have h := (near_distance_bounds hn).1
  norm_num [radius] at h
  linarith

theorem inverseDistanceBounds_sound {x : Fin 3 → ℝ} (hn : Near x) :
    inverseDistanceBounds.Contains (1/(distance x)^2) := by
  have h := near_distance_bounds hn
  have hp := near_distance_pos hn
  have hmin : (0:ℝ)<(1-4*radius:ℚ) := by norm_num [radius]
  have sl : ((1-4*radius:ℚ):ℝ)^2≤(distance x)^2 := by nlinarith [h.1]
  have sh : (distance x)^2≤((1+4*radius:ℚ):ℝ)^2 := by
    have hmax : (0:ℝ)<(1+4*radius:ℚ) := by norm_num [radius]
    nlinarith [h.2]
  have lo := one_div_le_one_div_of_le (sq_pos_of_pos hp) sh
  have hi := one_div_le_one_div_of_le (sq_pos_of_pos hmin) sl
  simpa only [inverseDistanceBounds,QInterval.Contains,Rat.cast_div,Rat.cast_one,
    Rat.cast_pow,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat] using And.intro lo hi

theorem bounds_sound {x : Fin 3 → ℝ} (hn : Near x) (i j : Fin 3) :
    (bounds i j).Contains (hessian exactMajorant x i j) := by
  have hu : |x 0|≤(radius:ℝ) := by simpa [center] using hn 0
  have hv : |x 1-1|≤(radius:ℝ) := by simpa [center] using hn 1
  have ht : |x 2|≤(radius:ℝ) := by simpa [center,Matrix.cons_val_two] using hn 2
  have hp := DenseKernel.bound_sound radius (polynomials i j) _ _ _ hu hv ht
  rw [polynomial_real] at hp
  have h := QInterval.add_sound hp
    (QInterval.scale_sound (ddQ i*ddQ j) (inverseDistanceBounds_sound hn))
  have hc (k : Fin 3) : (ddQ k:ℝ)=dd k := by fin_cases k <;> norm_num [ddQ,dd,Matrix.cons_val_two]
  convert h using 1
  dsimp [hessian]
  push_cast
  rw [hc,hc]
  ring

theorem near_hessian_posDef {x : Fin 3 → ℝ} (hn : Near x) :
    (hessian exactMajorant x).PosDef :=
  intervalMatrixCheck_sound bounds C U R D error checked _
    (hessian_isHermitian exactMajorant x) (bounds_sound hn)

theorem near_line {x : Fin 3 → ℝ} (hn : Near x) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    Near (line center (x-center) s) := by
  intro i
  change |center i+s*(x i-center i)-center i|≤(radius:ℝ)
  rw [show center i+s*(x i-center i)-center i=s*(x i-center i) by ring,
    abs_mul,abs_of_nonneg hs.1]
  simpa using mul_le_mul hs.2 (hn i) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)

theorem gap_center : gap exactMajorant center=0 := by
  have h := ContactCheck0.value_real
  norm_num [contactU,contactV,contactT,contactDistance,AlgebraicCoeff.one,
    AlgebraicCoeff.real,Matrix.cons_val_two] at h
  simpa [gap,eval3,distance,center,Matrix.cons_val_two] using h

theorem gradient_center_inward {x : Fin 3 → ℝ} (hx : 0≤x 0) :
    0≤∑ i,gradient exactMajorant center i*(x i-center i) := by
  have hv := ContactCheck0.dv_real
  have ht := ContactCheck0.dt_real
  have hu := ContactCheck0.normal_real_pos
  norm_num [contactU,contactV,contactT,contactDistance,AlgebraicCoeff.one,
    AlgebraicCoeff.real,Matrix.cons_val_two] at hv ht hu
  have h := mul_nonneg (le_of_lt (sub_pos.mpr hu)) hx
  simpa [gradient,eval3,partialPoly,distance,dd,center,Fin.sum_univ_succ,
    Matrix.cons_val_two,hv,ht] using h

/-- The boundary normal derivative is retained; only the inward half of the cube is asserted. -/
theorem near_gap_nonneg {x : Fin 3 → ℝ} (hn : Near x) (hx : 0≤x 0) :
    Real.log (distance x)≤exactMajorant.real (x 0) (x 1) (x 2) := by
  have h := gap_nonneg_of_segment exactMajorant center x gap_center
    (gradient_center_inward hx)
    (fun s hs => (near_distance_pos (near_line hn hs)).ne')
    (fun s hs => (near_hessian_posDef (near_line hn hs)).posSemidef)
  exact sub_nonneg.mp h

end MordellEight.CenterContact
