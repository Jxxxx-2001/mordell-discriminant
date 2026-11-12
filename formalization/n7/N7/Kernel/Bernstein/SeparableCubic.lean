-- Adapted from checked Eight/SeparableCubic.lean; point-count independent.
import N7.Kernel.Bernstein.CubicLeaf

namespace N7.Kernel.SeparableCubic
open FixedTensor IntegerCube RationalCube
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev Coeff := Fin 4 → Fin 4 → Fin 4 → Int
abbrev StageU := Fin 13 → Fin 4 → Fin 4 → Int
abbrev StageV := Fin 13 → Fin 13 → Fin 4 → Int

def coeff : List CubicLeaf.Term → Coeff
  | [] => fun _ _ _ => 0
  | a::ts => fun e f g =>
      (if e=a.i then if f=a.j then if g=a.k then a.coeff else 0 else 0 else 0)+coeff ts e f g

def b12 (e : Fin 4) (i : Fin 13) : Int := (CubicBasis.line12 e)[i.val]?.getD 0
def b6 (e : Fin 4) (i : Fin 7) : Int := (CubicBasis.line6 e)[i.val]?.getD 0

def computeU (c : Coeff) : StageU := fun i f g => ∑ e : Fin 4, c e f g*b12 e i
def computeV (u : StageU) : StageV := fun i j g => ∑ f : Fin 4, u i f g*b12 f j
def controls (v : StageV) : Cube :=
  List.ofFn fun i : Fin 13 => List.ofFn fun j : Fin 13 =>
    List.ofFn fun k : Fin 7 => ∑ g : Fin 4, v i j g*b6 g k

/-- Optional storage codecs only. The small C/U/V equalities below verify every
decoded integer, so no correctness assumption about these encodings is used. -/
def digit (bits : ℕ) (offset : Int) (n index : Nat) : Int :=
  Int.ofNat ((n >>> (index*bits)) &&& ((1 <<< bits)-1))-offset
def decodeCoeff (bits : ℕ) (offset : Int) (n : Nat) : Coeff :=
  fun e f g => digit bits offset n (e.val*16+f.val*4+g.val)
def decodeU (bits : ℕ) (offset : Int) (ns : List Nat) : StageU :=
  fun i f g => digit bits offset (ns[i.val]?.getD 0) (f.val*4+g.val)
def decodeV (bits : ℕ) (offset : Int) (ns : List Nat) : StageV :=
  fun i j g => digit bits offset (ns[i.val]?.getD 0) (j.val*4+g.val)

private theorem homogeneous_sum {A I : Type} (s : Finset I) (f : I → A → ℝ)
    (n : ℕ) (p : List A) (x y : ℝ) :
    homogeneous (fun a => ∑ i ∈ s, f i a) n p x y =
      ∑ i ∈ s, homogeneous (f i) n p x y := by
  induction p generalizing n with
  | nil => simp [homogeneous]
  | cons a p ih =>
    simp only [homogeneous,ih,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]

private theorem homogeneous_ofFn {A : Type} {m : ℕ} (f : Fin m → A) (e : A → ℝ)
    (n : ℕ) (x y : ℝ) :
    homogeneous e n (List.ofFn f) x y =
      homogeneous (fun i => e (f i)) n (List.ofFn (fun i : Fin m => i)) x y := by
  have h : (List.ofFn (fun i : Fin m => i)).map f=List.ofFn f := by simp [List.map_ofFn,Function.comp_def]
  rw [←h,homogeneous_map]

private theorem b12_value (e : Fin 4) (x : ℝ) :
    homogeneous (fun i : Fin 13 => (b12 e i : ℝ)) 12
      (List.ofFn (fun i : Fin 13 => i)) x (1-x)=x^e.val := by
  have h : List.ofFn (b12 e)=CubicBasis.line12 e := by fin_cases e <;> decide +kernel
  have hv := CubicBasis.line12_value e x
  rw [←h,homogeneous_ofFn] at hv
  exact hv

private theorem b6_value (e : Fin 4) (x : ℝ) :
    homogeneous (fun i : Fin 7 => (b6 e i : ℝ)) 6
      (List.ofFn (fun i : Fin 7 => i)) x (1-x)=x^e.val := by
  have h : List.ofFn (b6 e)=CubicBasis.line6 e := by fin_cases e <;> decide +kernel
  have hv := CubicBasis.line6_value e x
  rw [←h,homogeneous_ofFn] at hv
  exact hv

noncomputable def polynomial (c : Coeff) (u v t : ℝ) : ℝ :=
  ∑ g : Fin 4, ∑ f : Fin 4, ∑ e : Fin 4,
    (c e f g : ℝ)*u^e.val*v^f.val*t^g.val

theorem controls_value (c : Coeff) (u v t : ℝ) :
    (raw (controls (computeV (computeU c)))).bernEval 12 12 6 u v t = polynomial c u v t := by
  have raw_eval (p : Cube) :
      (raw p).bernEval 12 12 6 u v t =
      homogeneous (fun row => homogeneous (fun col =>
        homogeneous (fun z : Int => (z:ℝ)) 6 col t (1-t)) 12 row v (1-v)) 12 p u (1-u) := by
    unfold raw bernEval
    simp only [homogeneous_map, Rat.cast_intCast]
  rw [raw_eval]
  unfold controls computeV computeU polynomial
  simp only [homogeneous_ofFn, Int.cast_sum, Int.cast_mul]
  simp_rw [Finset.sum_mul]
  simp only [homogeneous_sum, CubicBasis.homogeneous_factor_left,
    CubicBasis.homogeneous_factor_right,b12_value,b6_value]

theorem coeff_value (ts : List CubicLeaf.Term) (u v t : ℝ) :
    polynomial (coeff ts) u v t=CubicLeaf.value u v t ts := by
  induction ts with
  | nil => simp [coeff,polynomial,CubicLeaf.value]
  | cons a ts ih =>
    have ih' := ih
    unfold polynomial at ih'
    simp only [mul_assoc] at ih'
    simp [coeff,polynomial,CubicLeaf.value,Int.cast_add,add_mul,
      Finset.sum_add_distrib,ite_mul,ih',mul_assoc]

theorem checked_value (ts : List CubicLeaf.Term) (c : Coeff) (u : StageU) (v : StageV)
    (hc : ∀ e f g, c e f g=coeff ts e f g)
    (hu : ∀ i f g, u i f g=computeU c i f g)
    (hv : ∀ i j g, v i j g=computeV u i j g) (x y z : ℝ) :
    (raw (controls v)).bernEval 12 12 6 x y z=CubicLeaf.value x y z ts := by
  have hce : c=coeff ts := funext fun e => funext fun f => funext fun g => hc e f g
  have hue : u=computeU c := funext fun i => funext fun f => funext fun g => hu i f g
  have hve : v=computeV u := funext fun i => funext fun j => funext fun g => hv i j g
  rw [hve,hue,hce,controls_value,coeff_value]

def gap (p : Cube) (A : Int) (v : StageV) : Cube :=
  IntegerCube.add (IntegerCube.scale A p) (controls v)

/-- Cubic and nonnegative Gram correction, for any certified tensor lower bound. -/
theorem majorant_of_value {p : Cube} {b : ClosedBox 3} {f : (Fin 3 → ℝ) → ℝ}
    (hw : b.Widths) (hm : TensorLower f b (decode p))
    (a l mu : ℚ) (A : Int) (ts : List CubicLeaf.Term)
    (c : Coeff) (u : StageU) (v : StageV)
    (hc : ∀ e f g, c e f g=coeff ts e f g)
    (hu : ∀ i f g, u i f g=computeU c i f g)
    (hv : ∀ i j g, v i j g=computeV u i j g)
    (hA : 0<A) (ha : 0<(a:ℝ)) (hl : Real.log (a:ℝ)≤(l:ℝ)) (hmu : 0≤mu)
    (hle : ∀ x, b.Contains x →
      CubicLeaf.value (b.coord x 0) (b.coord x 1) (b.coord x 2) ts ≤
        -((A:ℝ)*2^80)*(CubicLeaf.upper l ((x 0+x 1-2*x 2)/a-1)+
          (mu:ℝ)*(x 0*x 1-x 2^2)))
    (check : nonneg (gap p A v)=true)
    (x : Fin 3 → ℝ) (hx : b.Contains x)
    (hd : 0<x 0+x 1-2*x 2) (hg : x 2^2≤x 0*x 1) :
    Real.log (x 0+x 1-2*x 2)≤f x := by
  have hn := bernEval_nonneg (raw (gap p A v)) 12 12 6 (nonneg_sound _ check) _ _ _
    (ClosedBox.coord_unit hw hx 0) (ClosedBox.coord_unit hw hx 1) (ClosedBox.coord_unit hw hx 2)
  simp only [gap,raw_add,raw_scale,raw_decode p,(bernSound _ _ _ _ _ _).add,
    (bernSound _ _ _ _ _ _).scale,checked_value ts c u v hc hu hv] at hn
  push_cast at hn
  have hpos : 0<(A:ℝ)*2^80 := mul_pos (by exact_mod_cast hA) (by positivity)
  have hgap : 0≤(A:ℝ)*2^80*((decode p).boxEval b x-
      (CubicLeaf.upper l ((x 0+x 1-2*x 2)/a-1)+(mu:ℝ)*(x 0*x 1-x 2^2))) := by
    unfold boxEval
    linarith only [hn,hle x hx]
  have hbound := sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hpos).mp hgap)
  have hgram : 0≤(mu:ℝ)*(x 0*x 1-x 2^2) :=
    mul_nonneg (by exact_mod_cast hmu) (sub_nonneg.mpr hg)
  have hupp : CubicLeaf.upper l ((x 0+x 1-2*x 2)/a-1) ≤ (decode p).boxEval b x := by
    linarith only [hbound,hgram]
  exact (log_le_cubic hd ha hl).trans (hupp.trans (hm x hx))

theorem majorant {p : Cube} {b : ClosedBox 3} {f : (Fin 3 → ℝ) → ℝ}
    (hw : b.Widths) (hm : TensorLower f b (decode p))
    (a l mu : ℚ) (A : Int) (ts : List CubicLeaf.Term)
    (c : Coeff) (u : StageU) (v : StageV)
    (hc : ∀ e f g, c e f g=coeff ts e f g)
    (hu : ∀ i f g, u i f g=computeU c i f g)
    (hv : ∀ i j g, v i j g=computeV u i j g)
    (hA : 0<A) (ha : 0<(a:ℝ)) (hl : Real.log (a:ℝ)≤(l:ℝ)) (hmu : 0≤mu)
    (ident : ∀ x y z : ℝ, CubicLeaf.value x y z ts=
      -((A:ℝ)*2^80)*(CubicLeaf.upper l (CubicLeaf.dist b x y z/a-1)+
        (mu:ℝ)*CubicLeaf.gram b x y z))
    (check : nonneg (gap p A v)=true)
    (x : Fin 3 → ℝ) (hx : b.Contains x)
    (hd : 0<x 0+x 1-2*x 2) (hg : x 2^2≤x 0*x 1) :
    Real.log (x 0+x 1-2*x 2)≤f x := by
  apply majorant_of_value hw hm a l mu A ts c u v hc hu hv hA ha hl hmu ?_ check x hx hd hg
  intro y _
  rw [ident,CubicLeaf.dist_coords b hw y,CubicLeaf.gram_coords b hw y]

#print axioms controls_value
#print axioms majorant_of_value
#print axioms majorant
end N7.Kernel.SeparableCubic
