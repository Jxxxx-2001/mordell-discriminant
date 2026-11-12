import N7.Kernel.Domain
import N7.Kernel.Bernstein.ClosedCover

namespace N7.Kernel.Cover
set_option maxHeartbeats 0

def outsideCheck (b : ClosedBox 3) (reason : Nat) : Bool :=
  match reason with
  | 0 => decide (b.hi 1 < b.lo 0)
  | 1 => decide (b.hi 0+b.hi 1-2*b.lo 2 < 1/3)
  | 2 => decide (b.hi 2 < 0 ∧ b.hi 0*b.hi 1 < (b.hi 2)^2)
  | 3 => decide (0 < b.lo 2 ∧ b.hi 0*b.hi 1 < (b.lo 2)^2)
  | _ => false

theorem outsideCheck_sound (b : ClosedBox 3) (reason : Nat)
    (hc : outsideCheck b reason=true) (x : Fin 3 → ℝ) (hx : b.Contains x)
    (hd : PairDomain (x 0) (x 1) (x 2)) (ho : x 0≤x 1) : False := by
  rcases hd with ⟨hu,hv,_,_,hg,hd⟩
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have hb0 : (0:ℝ)≤b.hi 0 := hu.trans h0.2
  have hb1 : (0:ℝ)≤b.hi 1 := hv.trans h1.2
  have hp : x 0*x 1≤(b.hi 0:ℝ)*b.hi 1 := mul_le_mul h0.2 h1.2 hv hb0
  match reason with
  | 0 =>
    have hc' : b.hi 1 < b.lo 0 := of_decide_eq_true hc
    have hr : (b.hi 1:ℝ)<b.lo 0 := by exact_mod_cast hc'
    linarith
  | 1 =>
    have hc' : b.hi 0+b.hi 1-2*b.lo 2 < (1:ℚ)/3 := of_decide_eq_true hc
    have hr : ((b.hi 0+b.hi 1-2*b.lo 2:ℚ):ℝ) < ((1/3:ℚ):ℝ) := Rat.cast_lt.mpr hc'
    push_cast at hr
    linarith
  | 2 =>
    have hc' : b.hi 2 < 0 ∧ b.hi 0*b.hi 1 < (b.hi 2)^2 := of_decide_eq_true hc
    have hr0 : (b.hi 2:ℝ)<0 := by exact_mod_cast hc'.1
    have hr1 : (b.hi 0:ℝ)*b.hi 1<(b.hi 2:ℝ)^2 := by exact_mod_cast hc'.2
    nlinarith
  | 3 =>
    have hc' : 0 < b.lo 2 ∧ b.hi 0*b.hi 1 < (b.lo 2)^2 := of_decide_eq_true hc
    have hr0 : (0:ℝ)<b.lo 2 := by exact_mod_cast hc'.1
    have hr1 : (b.hi 0:ℝ)*b.hi 1<(b.lo 2:ℝ)^2 := by exact_mod_cast hc'.2
    nlinarith
  | n+4 => simp [outsideCheck] at hc

#print axioms outsideCheck_sound
end N7.Kernel.Cover
