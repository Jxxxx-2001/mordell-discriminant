import N7.Kernel.LocalGeometry
import N7.Kernel.Bernstein.ClosedCover

namespace N7.Kernel.Cover
def nearCheck (b : ClosedBox 3) (c : Fin 3 → ℚ) (r : ℚ) : Bool :=
  decide (∀ i, c i-r≤b.lo i ∧ b.hi i≤c i+r)

theorem nearCheck_sound (b : ClosedBox 3) (c : Fin 3 → ℚ) (r : ℚ)
    (hc : nearCheck b c r=true) {x : Fin 3 → ℝ} (hx : b.Contains x) :
    LocalGeometry.Near c r x := by
  have hh : ∀ i, c i-r≤b.lo i ∧ b.hi i≤c i+r := of_decide_eq_true hc
  intro i
  have hlo : (c i:ℝ)-(r:ℝ)≤b.lo i := by exact_mod_cast (hh i).1
  have hhi : (b.hi i:ℝ)≤(c i:ℝ)+(r:ℝ) := by exact_mod_cast (hh i).2
  exact abs_le.mpr ⟨by linarith [(hx i).1],by linarith [(hx i).2]⟩
end N7.Kernel.Cover
