import Eight.IntegerCube

namespace MordellEight.CubicBasis
open FixedTensor IntegerCube RationalCube
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Unnormalized degree-12 Bernstein coefficients of x^e. Entry i is
`choose (12-e) (i-e)` when e ≤ i, and zero otherwise. -/
def line12 (e : Fin 4) : List Int :=
  match e.val with
  | 0 => [1,12,66,220,495,792,924,792,495,220,66,12,1]
  | 1 => [0,1,11,55,165,330,462,462,330,165,55,11,1]
  | 2 => [0,0,1,10,45,120,210,252,210,120,45,10,1]
  | _ => [0,0,0,1,9,36,84,126,126,84,36,9,1]

/-- The same four monomials in unnormalized degree-6 Bernstein coordinates. -/
def line6 (e : Fin 4) : List Int :=
  match e.val with
  | 0 => [1,6,15,20,15,6,1]
  | 1 => [0,1,5,10,10,5,1]
  | 2 => [0,0,1,4,6,4,1]
  | _ => [0,0,0,1,3,3,1]

theorem line12_length (e : Fin 4) : (line12 e).length=13 := by
  fin_cases e <;> rfl

theorem line6_length (e : Fin 4) : (line6 e).length=7 := by
  fin_cases e <;> rfl

/-- Four small real polynomial identities, without any tensor expansion. -/
theorem line12_value (e : Fin 4) (x : ℝ) :
    homogeneous (fun z : Int => (z : ℝ)) 12 (line12 e) x (1-x)=x^e.val := by
  fin_cases e <;> norm_num [line12,homogeneous] <;> ring

/-- Four degree-6 identities. No interval assumption on x is needed. -/
theorem line6_value (e : Fin 4) (x : ℝ) :
    homogeneous (fun z : Int => (z : ℝ)) 6 (line6 e) x (1-x)=x^e.val := by
  fin_cases e <;> norm_num [line6,homogeneous] <;> ring

theorem homogeneous_factor_left {A : Type} (eval : A → ℝ) (c : ℝ)
    (n : ℕ) (p : List A) (x y : ℝ) :
    homogeneous (fun z => c*eval z) n p x y=c*homogeneous eval n p x y := by
  induction p generalizing n with
  | nil => simp [homogeneous]
  | cons a p ih => simp only [homogeneous,ih]; ring

theorem homogeneous_factor_right {A : Type} (eval : A → ℝ) (c : ℝ)
    (n : ℕ) (p : List A) (x y : ℝ) :
    homogeneous (fun z => eval z*c) n p x y=homogeneous eval n p x y*c := by
  induction p generalizing n with
  | nil => simp [homogeneous]
  | cons a p ih => simp only [homogeneous,ih]; ring

/-- A computable integer tensor for every trivariate monomial with each
exponent at most three. The tensor always has dimensions 13 × 13 × 7. -/
def controls (e f g : Fin 4) : Cube :=
  (line12 e).map fun a => (line12 f).map fun b => (line6 g).map fun c => a*b*c

/-- Separating the three factors avoids all 64 large polynomial expansions. -/
theorem value (e f g : Fin 4) (u v t : ℝ) :
    (raw (controls e f g)).bernEval 12 12 6 u v t=
      u^e.val*v^f.val*t^g.val := by
  have raw_eval (p : Cube) :
      (raw p).bernEval 12 12 6 u v t =
      homogeneous (fun row => homogeneous (fun col =>
        homogeneous (fun z : Int => (z:ℝ)) 6 col t (1-t)) 12 row v (1-v)) 12 p u (1-u) := by
    unfold raw bernEval
    simp only [homogeneous_map, Rat.cast_intCast]
  rw [raw_eval]
  unfold controls
  simp only [homogeneous_map, Int.cast_mul, homogeneous_factor_left, homogeneous_factor_right,
    line12_value, line6_value]
  all_goals trace_state

#print axioms value
end MordellEight.CubicBasis
