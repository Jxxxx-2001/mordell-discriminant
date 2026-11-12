import Eight.VerifiedContacts
import Eight.OuterContact.C1.Local
import Eight.OuterContact.C2.Local
import Eight.OuterContact.C3.Local
import Eight.DomainCover

namespace MordellEight
open Checks

def cubeContainmentCheck (b : ClosedBox 3) (c : Fin 3 → ℚ) (r : ℚ) : Bool :=
  decide (∀ i,c i-r≤b.lo i ∧ b.hi i≤c i+r)

theorem cubeContainmentCheck_sound (b : ClosedBox 3) (c : Fin 3 → ℚ) (r : ℚ)
    (hc : cubeContainmentCheck b c r=true) {x : Fin 3 → ℝ} (hx : b.Contains x) :
    ∀ i,|x i-(c i:ℝ)|≤(r:ℝ) := by
  intro i
  have h := of_decide_eq_true hc i
  have hl : (c i:ℝ)-(r:ℝ)≤(b.lo i:ℝ) := by exact_mod_cast h.1
  have hh : (b.hi i:ℝ)≤(c i:ℝ)+(r:ℝ) := by exact_mod_cast h.2
  exact abs_le.mpr ⟨by linarith [(hx i).1],by linarith [(hx i).2]⟩

def localLeafCheck (b : ClosedBox 3) (tag : Fin 5) : Bool :=
  match tag with
  | 0 => cubeContainmentCheck b ![0,1,0] CenterContact.radius
  | 1 => cubeContainmentCheck b ![1,0,0] CenterContact.radius
  | 2 => cubeContainmentCheck b ![1,1,OuterContact.C1.q] OuterContact.C1.radius
  | 3 => cubeContainmentCheck b ![1,1,OuterContact.C2.q] OuterContact.C2.radius
  | 4 => cubeContainmentCheck b ![1,1,OuterContact.C3.q] OuterContact.C3.radius

/-- A local leaf is accepted only when its whole closed box lies in a proved neighborhood. -/
theorem localLeafCheck_sound (b : ClosedBox 3) (tag : Fin 5)
    (hc : localLeafCheck b tag=true) {x : Fin 3 → ℝ}
    (hx : b.Contains x) (hd : PairDomain (x 0) (x 1) (x 2)) :
    Real.log (x 0+x 1-2*x 2)≤exactMajorant.real (x 0) (x 1) (x 2) := by
  rw [exact_majorant_eq_kernel]
  fin_cases tag
  · apply center_neighborhood_majorant ?_ hd.1
    have h := cubeContainmentCheck_sound b ![0,1,0] CenterContact.radius hc hx
    intro i
    fin_cases i
    · simpa [CenterContact.center,Matrix.cons_val_two] using h 0
    · simpa [CenterContact.center,Matrix.cons_val_two] using h 1
    · simpa [CenterContact.center,Matrix.cons_val_two] using h 2
  · apply swapped_center_neighborhood_majorant (u:=x 0) (v:=x 1) (t:=x 2) ?_ hd.2.1
    have h := cubeContainmentCheck_sound b ![1,0,0] CenterContact.radius hc hx
    intro i
    fin_cases i
    · simpa [CenterContact.center] using h 1
    · simpa [CenterContact.center] using h 0
    · simpa [CenterContact.center,Matrix.cons_val_two] using h 2
  · apply OuterContact.C1.majorant
    have h := cubeContainmentCheck_sound b ![1,1,OuterContact.C1.q] OuterContact.C1.radius hc hx
    intro i
    fin_cases i
    · simpa [OuterContact.rationalCenter,Matrix.cons_val_two] using h 0
    · simpa [OuterContact.rationalCenter,Matrix.cons_val_two] using h 1
    · simpa [OuterContact.rationalCenter,Matrix.cons_val_two] using h 2
  · apply OuterContact.C2.majorant
    have h := cubeContainmentCheck_sound b ![1,1,OuterContact.C2.q] OuterContact.C2.radius hc hx
    intro i
    fin_cases i
    · simpa [OuterContact.rationalCenter,Matrix.cons_val_two] using h 0
    · simpa [OuterContact.rationalCenter,Matrix.cons_val_two] using h 1
    · simpa [OuterContact.rationalCenter,Matrix.cons_val_two] using h 2
  · apply OuterContact.C3.majorant
    have h := cubeContainmentCheck_sound b ![1,1,OuterContact.C3.q] OuterContact.C3.radius hc hx
    intro i
    fin_cases i
    · simpa [OuterContact.rationalCenter,Matrix.cons_val_two] using h 0
    · simpa [OuterContact.rationalCenter,Matrix.cons_val_two] using h 1
    · simpa [OuterContact.rationalCenter,Matrix.cons_val_two] using h 2

end MordellEight
