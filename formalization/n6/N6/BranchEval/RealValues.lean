import N6.BranchEval.ProgramSoundness
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

namespace N6.BranchEval
open N6.SparseCheck

def onlyB (p : Poly) : Bool :=
  p.all (fun a => decide (a.1.t = 0 ∧ a.1.e = 0 ∧ a.1.k = 0 ∧ a.1.c = 0))

def bEval {R : Type*} [CommRing R] (B : R) : Poly → R
  | [] => 0
  | a :: p => (a.2 : R)*B^a.1.b + bEval B p

theorem value_eq_bEval {R : Type*} [CommRing R] (x : Fin 5 → R)
    (p : Poly) (hp : onlyB p = true) : value x p = bEval (x 4) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have hh : (a.1.t = 0 ∧ a.1.e = 0 ∧ a.1.k = 0 ∧ a.1.c = 0) ∧ onlyB p = true := by
      simpa only [onlyB, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] using hp
    rcases hh.1 with ⟨ht,he,hk,hc⟩
    simp only [value, bEval, monVal, ht, he, hk, hc, pow_zero, one_mul, ih hh.2]

theorem bEval_ofReal (B : ℝ) (p : Poly) :
    bEval (B : ℂ) p = ((bEval (R := ℝ) B p : ℝ) : ℂ) := by
  induction p with
  | nil => simp only [bEval, Complex.ofReal_zero]
  | cons a p ih =>
    simp only [bEval, ih, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_intCast]

noncomputable def realNF (B : ℝ) (a : Program.NF) : ℝ :=
  algebraMap ℚ ℝ ((a.den : ℚ)⁻¹) * bEval B a.num

theorem rat_algebraMap_ofReal (q : ℚ) :
    algebraMap ℚ ℂ q = ((algebraMap ℚ ℝ q : ℝ) : ℂ) := by
  simpa only [Complex.ofRealHom_eq_coe] using
    (RingHom.map_rat_algebraMap Complex.ofRealHom q).symm

theorem meaning_of_real_B (x : Fin 5 → ℂ) (a : Program.NF) (B : ℝ)
    (hp : onlyB a.num = true) (hB : x 4 = (B : ℂ)) :
    Program.meaning x a = (realNF B a : ℂ) := by
  rw [Program.meaning, value_eq_bEval x a.num hp, hB, bEval_ofReal]
  simp only [realNF, Complex.ofReal_mul]
  rw [rat_algebraMap_ofReal]

def ratEval {K : Type*} [Field K] [CharZero K] (p : List ℚ) (a : K) : K :=
  p.foldr (fun q r => algebraMap ℚ K q + a*r) 0

theorem ratEval_ofReal (p : List ℚ) (a : ℝ) :
    ratEval p (a : ℂ) = ((ratEval (K := ℝ) p a : ℝ) : ℂ) := by
  induction p with
  | nil => simp [ratEval]
  | cons q p ih =>
    simp only [ratEval, List.foldr_cons] at ih ⊢
    rw [ih, Complex.ofReal_add, Complex.ofReal_mul, rat_algebraMap_ofReal]

#print axioms meaning_of_real_B
#print axioms ratEval_ofReal
end N6.BranchEval
