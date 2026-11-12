import N7.Kernel.Checks.IntervalMatrix

set_option autoImplicit false
namespace N7.Kernel.LocalSchur
open Matrix N7.Kernel.Checks
set_option maxHeartbeats 1200000

noncomputable def pivot1 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := A 1 1-(A 0 1)^2/A 0 0
noncomputable def cross1 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := A 1 2-A 0 1*A 0 2/A 0 0
noncomputable def pivot2 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  A 2 2-(A 0 2)^2/A 0 0-(cross1 A)^2/pivot1 A

theorem psd_of_pivots (A : Matrix (Fin 3) (Fin 3) ℝ) (hs : A.IsHermitian)
    (h0 : 0<A 0 0) (h1 : 0<pivot1 A) (h2 : 0≤pivot2 A) : A.PosSemidef := by
  have hsym (i j : Fin 3) : A j i=A i j := by
    have h := congrFun (congrFun hs i) j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using h
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hs
  intro x
  have he : x ⬝ᵥ (A*ᵥx) =
      A 0 0*(x 0+(A 0 1/A 0 0)*x 1+(A 0 2/A 0 0)*x 2)^2+
      pivot1 A*(x 1+(cross1 A/pivot1 A)*x 2)^2+pivot2 A*(x 2)^2 := by
    simp only [dotProduct,Matrix.mulVec,Fin.sum_univ_succ,Fin.sum_univ_zero,
      Fin.succ_zero_eq_one,Fin.succ_one_eq_two,add_zero]
    rw [hsym 0 1,hsym 0 2,hsym 1 2]
    have ha : A 0 0≠0 := h0.ne'
    have hb : pivot1 A≠0 := h1.ne'
    simp only [pivot2,pivot1,cross1] at hb ⊢
    have hd : A 0 0*A 1 1-(A 0 1)^2≠0 := by
      have ht := (div_lt_iff₀ h0).mp (sub_pos.mp h1)
      nlinarith
    field_simp [ha,hb,hd]
    <;> ring
  simp only [star_trivial]
  rw [he]
  exact add_nonneg (add_nonneg (mul_nonneg h0.le (sq_nonneg _))
    (mul_nonneg h1.le (sq_nonneg _))) (mul_nonneg h2 (sq_nonneg _))

def neg (a : QInterval) : QInterval := a.scale (-1)
def sub (a b : QInterval) : QInterval := a.add (neg b)
def inv (a : QInterval) : QInterval := ⟨1/a.hi,1/a.lo⟩
def div (a b : QInterval) : QInterval := a.mul (inv b)
def sq (a : QInterval) : QInterval := a.mul a

theorem sub_sound {a b : QInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (sub a b).Contains (x-y) := by
  have h := QInterval.add_sound hx (QInterval.scale_sound (-1) hy)
  simpa [sub,neg,sub_eq_add_neg] using h

theorem inv_sound {a : QInterval} {x : ℝ} (ha : 0<a.lo) (hx : a.Contains x) :
    (inv a).Contains (1/x) := by
  have hlo : (0:ℝ)<a.lo := by exact_mod_cast ha
  have hp : 0<x := hlo.trans_le hx.1
  have hlow := one_div_le_one_div_of_le hp hx.2
  have hhigh := one_div_le_one_div_of_le hlo hx.1
  simpa only [inv,QInterval.Contains,Rat.cast_div,Rat.cast_one] using And.intro hlow hhigh

theorem div_sound {a b : QInterval} {x y : ℝ} (hb : 0<b.lo)
    (hx : a.Contains x) (hy : b.Contains y) : (div a b).Contains (x/y) := by
  simpa [div,div_eq_mul_inv] using QInterval.mul_sound hx (inv_sound hb hy)

theorem sq_sound {a : QInterval} {x : ℝ} (hx : a.Contains x) : (sq a).Contains (x^2) := by
  simpa [sq,pow_two] using QInterval.mul_sound hx hx

def bound1 (B : Matrix (Fin 3) (Fin 3) QInterval) : QInterval :=
  sub (B 1 1) (div (sq (B 0 1)) (B 0 0))
def boundCross (B : Matrix (Fin 3) (Fin 3) QInterval) : QInterval :=
  sub (B 1 2) (div ((B 0 1).mul (B 0 2)) (B 0 0))
def bound2 (B : Matrix (Fin 3) (Fin 3) QInterval) : QInterval :=
  sub (sub (B 2 2) (div (sq (B 0 2)) (B 0 0))) (div (sq (boundCross B)) (bound1 B))

def check (B : Matrix (Fin 3) (Fin 3) QInterval) : Bool :=
  decide (0<(B 0 0).lo ∧ 0<(bound1 B).lo ∧ 0≤(bound2 B).lo)

theorem check_sound (B : Matrix (Fin 3) (Fin 3) QInterval) (hc : check B=true)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hs : A.IsHermitian)
    (hB : ∀ i j,(B i j).Contains (A i j)) : A.PosSemidef := by
  have h := of_decide_eq_true hc
  have h1 : (bound1 B).Contains (pivot1 A) :=
    sub_sound (hB 1 1) (div_sound h.1 (sq_sound (hB 0 1)) (hB 0 0))
  have hcross : (boundCross B).Contains (cross1 A) :=
    sub_sound (hB 1 2) (div_sound h.1 (QInterval.mul_sound (hB 0 1) (hB 0 2)) (hB 0 0))
  have h2 : (bound2 B).Contains (pivot2 A) :=
    sub_sound (sub_sound (hB 2 2) (div_sound h.1 (sq_sound (hB 0 2)) (hB 0 0)))
      (div_sound h.2.1 (sq_sound hcross) h1)
  apply psd_of_pivots A hs
  · have hh : (0:ℝ)<(B 0 0).lo := by exact_mod_cast h.1
    exact hh.trans_le (hB 0 0).1
  · have hh : (0:ℝ)<(bound1 B).lo := by exact_mod_cast h.2.1
    exact hh.trans_le h1.1
  · have hh : (0:ℝ)≤(bound2 B).lo := by exact_mod_cast h.2.2
    exact hh.trans h2.1

#print axioms check_sound
end N7.Kernel.LocalSchur
